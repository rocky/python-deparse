#!/usr/bin/env python
'Unit test for trepan.processor.command.deparse'

import os, sys, unittest, inspect


from trepan_deparse import deparser

class TestBreakCommand(unittest.TestCase):

    def test_basic(self):
        deparser.deparse_test(inspect.currentframe().f_code)
        self.assertEqual(True, True, "testing")
        return

if __name__ == '__main__':
    unittest.main()
