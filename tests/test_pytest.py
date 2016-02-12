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

from unittest.mock import MagicMock

import pytest

from katal import katal

@pytest.fixture(autouse=True)
def tmp_target_dir(tmpdir):
    katal.ARGS = MagicMock()
    katal.ARGS.targetpath = tmpdir
    return tmpdir


def test_initialization(tmp_target_dir):
    args = '-cfg tests/cfgfile1.ini'.split()

    try:
        katal.main(args)
    except SystemExit as system_exit:
        assert not system_exit.code


    path = tmp_target_dir.join(katal.CST__KATALSYS_SUBDIR)
    for p in ['', katal.CST__LOG_SUBSUBDIR, katal.CST__TRASH_SUBSUBDIR,
              katal.CST__TASKS_SUBSUBDIR]:

        assert path.join(p).ensure(dir=True)

    assert path.join(katal.get_logfile_fullname()).ensure()

