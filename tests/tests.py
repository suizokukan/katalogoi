#!/usr/bin/env python3
# -*- coding: utf-8 -*-
################################################################################
#    Katal Copyright (C) 2012 Suizokukan
#    Contact: suizokukan _A.T._ orange dot fr
#
#    This file is part of Katal.
#    Katal is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    Katal is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with Katal.  If not, see <http://www.gnu.org/licenses/>.
################################################################################
"""
       Katal by suizokukan (suizokukan AT orange DOT fr)

       tests.py
"""
# Pylint : disabling the "Class 'ARGS' has no 'configfile' member" error
#          since there IS a 'configfile' member for the ARGS class.
# pylint: disable=E1101

from collections import namedtuple
import os
import unittest

from katal import katal
katal.ARGS = namedtuple("ARGS", ("configfile", "verbosity", "targetpath",))
katal.ARGS.verbosity = 'none'
katal.ARGS.targetpath = "tests"
katal.ARGS.usentfsprefix = None

################################################################################
class Tests(unittest.TestCase):
    """
        Tests class

	Testing the katal.py script
    """

    #//////////////////////////////////////////////////////////////////////////
    def test__fill_select1(self):
        """
		Tests.test__fill_select1()

		Test of the katal.py::fill_select() function.
        """
        config = katal.Config()
        config.read_config(args=None, cfg_file=os.path.join("tests", "cfgfile1.ini"))
        katal.CFG_PARAMETERS = config
        katal.ARGS = config
        katal.CONFIG = config
        katal.SOURCE_PATH = os.path.join("tests", "data1")
        katal.read_filters()
        katal.fill_select()

        self.assertEqual(len(katal.SELECT), 1)

        # hashid of b.2 :
        hashid = list(katal.SELECT.keys())[0]
        self.assertTrue(katal.SELECT[hashid].fullname, "b.2")

   #//////////////////////////////////////////////////////////////////////////
    def test__fill_select2(self):
        """
		Tests.test__fill_select2()

		Test of the katal.py::fill_select() function.
        """
        config = katal.Config()
        config.read_config(args=None, cfg_file=os.path.join("tests", "cfgfile2.ini"))
        katal.CFG_PARAMETERS = config
        katal.ARGS = config
        katal.CONFIG = config
        katal.read_filters()
        katal.fill_select()

        self.assertEqual(len(katal.SELECT), 1)

        # hashid of b.2 = b.3
        hashid = "O2TblctVx2M5HHBxCEia4YtBEteDMA3jjgM7TJjD3q8="
        self.assertTrue(hashid in katal.SELECT)

    #//////////////////////////////////////////////////////////////////////////
    def test__fill_select3(self):
        """
		Tests.test__fill_select3()

		Test of the katal.py::fill_select() function.
        """
        config = katal.Config()
        config.read_config(args=None, cfg_file=os.path.join("tests", "cfgfile3.ini"))
        katal.CFG_PARAMETERS = config
        katal.ARGS = config
        katal.CONFIG = config
        katal.SOURCE_PATH = os.path.join("tests", "data1")
        katal.read_filters()
        katal.fill_select()

        # hashid of C.5 :
        hashid = "11TnbVxzyXGjz0LwAjC804And9dqVLWcFUJxApkS12I="
        self.assertTrue(hashid in katal.SELECT)

        # hashid of c.5 == c.4
        hashid = "rc2y98HRxM0xEpm9nouE60nVk4TUq3ec9sr10UEwpnY="
        self.assertTrue(hashid in katal.SELECT)

        # hashid of a.1 == a.0
        hashid = "47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU="
        self.assertTrue(hashid in katal.SELECT)

    #//////////////////////////////////////////////////////////////////////////
    def test__fill_select4(self):
        """
		Tests.test__fill_select4()

		Test of the katal.py::fill_select() function.
        """
        config = katal.Config()
        katal.ARGS = config
        katal.CONFIG = config
        config.read_config(args=None, cfg_file=os.path.join("tests", "cfgfile4.ini"))
        katal.CFG_PARAMETERS = config
        katal.SOURCE_PATH = os.path.join("tests", "data1")
        katal.read_filters()
        katal.fill_select()

        self.assertEqual(len(katal.SELECT), 1)

        # hashid of ddddd.6 = ddddX.6
        hashid = "47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU="
        self.assertTrue(hashid in katal.SELECT)

    #//////////////////////////////////////////////////////////////////////////
    def test__fill_select5(self):
        """
		Tests.test__fill_select5()

		Test of the katal.py::fill_select() function.
        """
        config = katal.Config()
        katal.ARGS = config
        katal.CONFIG = config
        config.read_config(args=None, cfg_file=os.path.join("tests", "cfgfile5.ini"))
        katal.CFG_PARAMETERS = config
        katal.SOURCE_PATH = os.path.join("tests", "data1")
        katal.read_filters()
        katal.fill_select()

        #for k in katal.SELECT:
        #    print(k, katal.SELECT[k].fullname)

        self.assertEqual(len(katal.SELECT), 2)

        # hashid of c.5 == c.4 :
        hashid = "rc2y98HRxM0xEpm9nouE60nVk4TUq3ec9sr10UEwpnY="
        self.assertTrue(hashid in katal.SELECT)

        # hashid of C.5 :
        hashid = "11TnbVxzyXGjz0LwAjC804And9dqVLWcFUJxApkS12I="
        self.assertTrue(hashid in katal.SELECT)
