import uncompyle2
from uncompyle2 import uncompyle, walker, verify, magics
import sys, inspect, types, cStringIO, re


# FIXME: remove uncompyle dups
# from uncompyle2.walker import find_all_globals, find_globals, find_none
from uncompyle2.walker import *
from uncompyle2.spark import GenericASTTraversal, GenericASTTraversalPruningException
from types import ListType, TupleType, DictType, \
     EllipsisType, IntType, CodeType
from scanner import Token, Code

from collections import namedtuple
NodeInfo = namedtuple("NodeInfo", "node start finish")
ExtractInfo = namedtuple("ExtractInfo",
                         "lineNo lineStartOffset markerLine selectedLine selectedText")

class FindWalker(walker.Walker, object):
    stacked_params = ('f', 'indent', 'isLambda', '_globals')

    def __init__(self, out, scanner, showast=0):
        GenericASTTraversal.__init__(self, ast=None)
        self.scanner = scanner
        params = {
            'f': out,
            'indent': '',
            }
        self.showast = showast
        self.__params = params
        self.__param_stack = []
        self.ERROR = None
        self.prec = 100
        self.return_none = False
        self.mod_globs = set()
        self.currentclass = None
        self.pending_newlines = 0

        self.found_offset = False
        self.offsets = {}


    f = property(lambda s: s.__params['f'],
                 lambda s, x: s.__params.__setitem__('f', x),
                 lambda s: s.__params.__delitem__('f'),
                 None)

    indent = property(lambda s: s.__params['indent'],
                 lambda s, x: s.__params.__setitem__('indent', x),
                 lambda s: s.__params.__delitem__('indent'),
                 None)

    isLambda = property(lambda s: s.__params['isLambda'],
                 lambda s, x: s.__params.__setitem__('isLambda', x),
                 lambda s: s.__params.__delitem__('isLambda'),
                 None)

    _globals = property(lambda s: s.__params['_globals'],
                 lambda s, x: s.__params.__setitem__('_globals', x),
                 lambda s: s.__params.__delitem__('_globals'),
                 None)

    def make_function(self, node, isLambda, nested=1):
        """Dump function defintion, doc string, and function body."""

        def build_param(ast, name, default):
            """build parameters:
                - handle defaults
                - handle format tuple parameters
            """
            # if formal parameter is a tuple, the paramater name
            # starts with a dot (eg. '.1', '.2')
            if name.startswith('.'):
                # replace the name with the tuple-string
                name = self.get_tuple_parameter(ast, name)

            if default:
                if self.showast:
                    print '--', name
                    print default
                    print '--'
                result = '%s = %s' % (name, self.traverse(default, indent='') )
                if result[-2:] == '= ':	# default was 'LOAD_CONST None'
                    result += 'None'
                return result
            else:
                return name
        defparams = node[:node[-1].attr] # node[-1] == MAKE_xxx_n
        code = node[-2].attr

        assert type(code) == CodeType
        code = Code(code, self.scanner, self.currentclass)
        #assert isinstance(code, Code)

        # add defaults values to parameter names
        argc = code.co_argcount
        paramnames = list(code.co_varnames[:argc])

        # defaults are for last n parameters, thus reverse
        paramnames.reverse(); defparams.reverse()

        try:
            ast = self.build_ast(code._tokens,
                                 code._customize,
                                 isLambda = isLambda,
                                 noneInNames = ('None' in code.co_names))
        except ParserError as p:
            self.write( str(p))
            self.ERROR = p
            return

        # build parameters

        ##This would be a nicer piece of code, but I can't get this to work
        ## now, have to find a usable lambda constuct  hG/2000-09-05
        ##params = map(lambda name, default: build_param(ast, name, default),
        ##	     paramnames, defparams)
        params = []
        for name, default in map(lambda a,b: (a,b), paramnames, defparams):
            params.append( build_param(ast, name, default) )

        params.reverse() # back to correct order

        if 4 & code.co_flags:	# flag 2 -> variable number of args
            params.append('*%s' % code.co_varnames[argc])
            argc += 1
        if 8 & code.co_flags:	# flag 3 -> keyword args
            params.append('**%s' % code.co_varnames[argc])
            argc += 1

        # dump parameter list (with default values)
        indent = self.indent
        if isLambda:
            self.write("lambda ", ", ".join(params), ": ")
        else:
            self.print_("(", ", ".join(params), "):")
            #self.print_(indent, '#flags:\t', int(code.co_flags))

        if len(code.co_consts)>0 and code.co_consts[0] != None and not isLambda: # ugly
            # docstring exists, dump it
            self.print_docstring(indent, code.co_consts[0])


        code._tokens = None # save memory
        assert ast == 'stmts'
        #if isLambda:
            # convert 'return' statement to expression
            #assert len(ast[0]) == 1  wrong, see 'lambda (r,b): r,b,g'
            #assert ast[-1] == 'stmt'
            #assert len(ast[-1]) == 1
#            assert ast[-1][0] == 'return_stmt'
#            ast[-1][0].type = 'return_lambda'
        #else:
        #    if ast[-1] == RETURN_NONE:
                # Python adds a 'return None' to the
                # end of any function; remove it
         #       ast.pop() # remove last node

        all_globals = find_all_globals(ast, set())
        for g in ((all_globals & self.mod_globs) | find_globals(ast, set())):
           self.print_(self.indent, 'global ', g)
        self.mod_globs -= all_globals
        rn = ('None' in code.co_names) and not find_none(ast)
        self.gen_source(ast, code._customize, isLambda=isLambda, returnNone=rn)
        code._tokens = None; code._customize = None # save memory

    def n_return_stmt(self, node):
        if self.__params['isLambda']:
            self.preorder(node[0])
            self.prune()
        else:
            self.write(self.indent, 'return')
            if self.return_none or node != AST('return_stmt', [AST('ret_expr', [NONE]), Token('RETURN_VALUE')]):
                self.write(' ')
                self.preorder(node[0])
            self.print_()
            self.prune() # stop recursing

    def n_return_if_stmt(self, node):
        if self.__params['isLambda']:
            self.preorder(node[0])
            self.prune()
        else:
            self.write(self.indent, 'return')
            if self.return_none or node != AST('return_stmt', [AST('ret_expr', [NONE]), Token('RETURN_END_IF')]):
                self.write(' ')
                self.preorder(node[0])
            self.print_()
            self.prune() # stop recursing

    def n_mkfunc(self, node):
        self.write(node[-2].attr.co_name) # = code.co_name
        self.indentMore()
        self.make_function(node, isLambda=0)
        if len(self.__param_stack) > 1:
            self.write('\n\n')
        else:
            self.write('\n\n\n')
        self.indentLess()
        self.prune() # stop recursing

    def preorder(self, node=None):
        if node is None:
            node = self.ast

        if hasattr(node, 'offset'):
            start = len(self.f.getvalue())
            if node.offset == self.find_offset:
                self.found_offset = True
                # print 'BINGO!'

        try:
            name = 'n_' + self.typestring(node)
            if hasattr(self, name):
                func = getattr(self, name)
                func(node)
            else:
                self.default(node)
        except GenericASTTraversalPruningException:
            # All leaf nodes, those with the offset method among others
            # seems to fit under this exception. If this is not true
            # we would need to dupllicate the below code before the
            # return outside of this block
            if hasattr(node, 'offset'):
                self.offsets[node.offset] = NodeInfo(node = node,
                                                     start = start,
                                                     finish = len(self.f.getvalue()))
                # print self.offsets[node.offset]
                # print self.f.getvalue()[start:]
            return

        for kid in node:
            self.preorder(kid)

        name = name + '_exit'
        if hasattr(self, name):
            func = getattr(self, name)
            func(node)

        return


    def find_source(self, offset, ast, customize, isLambda=0, returnNone=False):
        """convert AST to source code"""

        self.find_offset = offset
        self.found_offset = False

        # FIXME; the below doesn't find self.__params
        # So we duplicate the code.
        # self.gen_source(ast, customize, isLambda, returnNone)
        rn = self.return_none
        self.return_none = returnNone
        # if code would be empty, append 'pass'
        if len(ast) == 0:
            self.print_(self.indent, 'pass')
        else:
            self.customize(customize)
            self.text = self.traverse(ast, isLambda=isLambda)
        self.return_none = rn

    # FIXME; below duplicated the code, since we don't find self.__params
    def traverse(self, node, indent=None, isLambda=0):

        self.__param_stack.append(self.__params)
        if indent is None: indent = self.indent
        p = self.pending_newlines
        self.pending_newlines = 0
        self.__params = {
            '_globals': {},
            'f': cStringIO.StringIO(),
            'indent': indent,
            'isLambda': isLambda,
            }
        self.preorder(node)
        self.f.write('\n'*self.pending_newlines)

        text = self.f.getvalue()

        self.__params = self.__param_stack.pop()
        self.pending_newlines = p
        return text

    def extract_line_info(self, offset):
        if offset not in self.offsets.keys():
            return None

        nodeInfo  = self.offsets[offset]
        start, finish = (nodeInfo.start, nodeInfo.finish)
        text = self.text
        selectedText = text[start: finish]
        # if selectedText == 'co':
        #     from trepan.api import debug; debug()

        try:
            lineStart = text[:finish].rindex("\n") + 1
        except ValueError:
            lineStart = 0

        try:
            lineEnd = lineStart + text[lineStart+1:].index("\n") - 1
        except ValueError:
            lineEnd = len(text)

        adjustedStart = start - lineStart
        adjustedFinish = finish - lineStart

        # if offset == 133:
        #     from trepan.api import debug; debug()
        leadBlankMatch = re.match('^([ \n]+)',  selectedText)
        if leadBlankMatch:
            blankCount = len(leadBlankMatch.group(0))
        else:
            blankCount = 0

        markerLine = ((' ' * (adjustedStart + blankCount)) +
                      ('-' * (len(selectedText) - blankCount)))
        lines = text[:lineEnd].split("\n")
        selectedLine = text[lineStart:lineEnd+2]

        return ExtractInfo(lineNo = len(lines), lineStartOffset = lineStart,
                           markerLine = markerLine,
                           selectedLine = selectedLine,
                           selectedText = selectedText)


    pass

def uncompyle_find(version, co, find_offset, out=sys.stdout, showasm=0, showast=0):
    assert type(co) == types.CodeType
    # store final output stream for case of error
    __real_out = out or sys.stdout
    if version == 2.7:
        import uncompyle2.scanner27 as scan
        scanner = scan.Scanner27()
    elif version == 2.6:
        import scanner26 as scan
        scanner = scan.Scanner26()
    elif version == 2.5:
        import scanner25 as scan
        scanner = scan.Scanner25()
    scanner.setShowAsm(0, out)
    tokens, customize = scanner.disassemble(co)

    #  Build AST from disassembly.
    # walk = walker.Walker(out, scanner, showast=showast)
    walk = FindWalker(out, scanner, showast=showast)

    try:
        ast = walk.build_ast(tokens, customize)
    except walker.ParserError, e :  # parser failed, dump disassembly
        print >>__real_out, e
        raise
    del tokens # save memory

    # convert leading '__doc__ = "..." into doc string
    assert ast == 'stmts'
    try:
        if ast[0][0] == walker.ASSIGN_DOC_STRING(co.co_consts[0]):
            if find_offset == 0:
                walk.print_docstring('', co.co_consts[0])
                return
            del ast[0]
        if ast[-1] == walker.RETURN_NONE:
            ast.pop() # remove last node
            #todo: if empty, add 'pass'
    except:
        pass
    walk.mod_globs = walker.find_globals(ast, set())
    # walk.gen_source(ast, customize)
    walk.find_source(find_offset, ast, customize)
    for g in walk.mod_globs:
        walk.write('global %s ## Warning: Unused global' % g)
    if walk.ERROR:
        raise walk.ERROR

    return walk

def uncompyle_test():
    frame = inspect.currentframe()
    try:
        co = frame.f_code
        # uncompyle(2.7, co, sys.stdout, 1)
        walk = uncompyle_find(2.7, co, 33)
        print walk.text, "\n"
        print '------------------------'
        for offset in sorted(walk.offsets.keys()):
            print("offset %d" % offset)
            extractInfo = walk.extract_line_info(offset)
            # print extractInfo
            print extractInfo.selectedText
            print extractInfo.selectedLine
            print extractInfo.markerLine


    finally:
        del frame

if __name__ == '__main__':
    uncompyle_test()
