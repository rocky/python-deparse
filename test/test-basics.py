#!/usr/bin/env python
'Unit test for deparser maps'

from __future__ import print_function

import os, sys, unittest, inspect
from sys import version_info
from inspect import getmembers, isfunction

from trepan_deparse import deparser

class TestMaps(unittest.TestCase):

    def setup(self):
        self.sys_version = version_info.major + (version_info.minor / 10.0)

    def map_stmts(x, y):
        x = []
        y = {}

    def return_stmt(x, y):
            return x, y

    def try_stmt():
        try:
            x = 1
        except:
            pass

    def for_range_stmt():
        for i in range(2):
            i+1

    def get_parsed_for_fn(self, fn):
        return deparser.deparse(self.sys_version,
                                getmembers(fn, isfunction)[0][1].func_code)

    def check_expect(self, expect, parsed):
        debug = False
        i = 2
        max_expect = len(expect)
        for name, offset in sorted(parsed.offsets.keys()):
            self.assertTrue(i+1 <= max_expect, "ran out if items in testing node")
            nodeInfo = parsed.offsets[name, offset]
            node = nodeInfo.node
            extractInfo = parsed.extract_node_info(node)

            self.assertEqual(expect[i], extractInfo.selectedLine,
                             'line %s expect:\n%s\ngot:s\n%s' %
                             (i, expect[i], extractInfo.selectedLine))
            self.assertEqual(expect[i+1], extractInfo.markerLine,
                             'line %s expect:\n%s\ngot:\n%s' %
                             (i+1, expect[i+1], extractInfo.markerLine))
            i += 3
            if debug:
                print(node.offset)
                print(extractInfo.selectedLine)
                print(extractInfo.markerLine)

            extractInfo, p = parsed.extract_parent_info(node)
            if extractInfo:
                self.assertTrue(i+1 < max_expect, "ran out of items in testing parent")
                self.assertEqual(expect[i], extractInfo.selectedLine,
                                 "parent line %s expect:\n%s\ngot:\n%s" %
                                 (i, expect[i], extractInfo.selectedLine))
                self.assertEqual(expect[i+1], extractInfo.markerLine,
                                 "parent line %s expect:\n%s\ngot:\n%s" %
                                 (i+1, expect[i+1], extractInfo.markerLine))
                if debug:
                    print("Contained in...")
                    print(extractInfo.selectedLine)
                    print(extractInfo.markerLine)
                i += 3
            pass
        pass


    def test_stuff(self):
        self.setup()
        parsed = self.get_parsed_for_fn(self.map_stmts)
        expect = """
0
x = []
    --
Contained in...
x = []
------
3
x = []
-
Contained in...
x = []
------
6
y = {}
    --
Contained in...
y = {}
------
9
y = {}
-
Contained in...
y = {}
------
""".split("\n")
        self.check_expect(expect, parsed)
        ########################################################
        # return

        parsed = self.get_parsed_for_fn(self.return_stmt)
        expect = """
-1
return (x, y)
             ^
Contained in...
return (x, y)
-------------
0
return (x, y)
        -
Contained in...
return (x, y)
       ------
3
return (x, y)
           -
Contained in...
return (x, y)
       ------
6
return (x, y)
       ------
Contained in...
return (x, y)
-------------
9
return (x, y)
-------------
Contained in...
return (x, y)
-------------
""".split("\n")
        self.check_expect(expect, parsed)
        ########################################################
        # try

        expect = """
0
try:
----
Contained in...
try: ...
---- ...
3
    x = 1
        -
Contained in...
    x = 1
    -----
6
    x = 1
    -
Contained in...
    x = 1
    -----
9
    pass
        ^
Contained in...
try: ...
---- ...
10
except:
        ^
Contained in...
except: ...
------- ...
19
    pass
        ^
Contained in...
except: ...
------- ...
13_0
except:
        ^
Contained in...
except: ...
------- ...
20_0
    pass
        ^
Contained in...
except: ...
------- ...
""".split("\n")
        parsed = self.get_parsed_for_fn(self.try_stmt)
        self.check_expect(expect, parsed)

        ########################################################
        # for range
        expect = """
0
for i in range(2):
    -
Contained in...
for i in range(2): ...
------------------ ...
3
for i in range(2):
         -----
Contained in...
for i in range(2):
         --------
6
for i in range(2):
               -
Contained in...
for i in range(2):
         --------
12
for i in range(2):
    -
Contained in...
for i in range(2): ...
------------------ ...
13
for i in range(2):
    -
Contained in...
for i in range(2): ...
------------------ ...
16
for i in range(2):
    -
Contained in...
for i in range(2): ...
------------------ ...
19
    i + 1
    -
Contained in...
    i + 1
    -----
22
    i + 1
        -
Contained in...
    i + 1
    -----
25
    i + 1
      -
Contained in...
    i + 1
    -----
27
    i + 1
         ^
Contained in...
    i + 1
    -----
""".split("\n")
        parsed = self.get_parsed_for_fn(self.for_range_stmt)
        self.check_expect(expect, parsed)

        return


if __name__ == '__main__':
    unittest.main()
