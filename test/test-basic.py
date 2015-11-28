#!/usr/bin/env python
'Unit test for trepan.processor.command.deparse'

import os, sys, unittest


from trepan_deparse import deparse

class TestBreakCommand(unittest.TestCase):

    def test_basic(self):
        deparse.uncompyle_test()
        self.assertEqual(True, True, "testing")
        return

if __name__ == '__main__':
    unittest.main()
