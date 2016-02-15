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
import os
from datetime import datetime
import random

import pytest

from katal import katal

def populate(path, name, time=None, size=0):
    p = path.join(name)
    # Random, else every file has the same hashid
    with p.open('w') as f:
        f.seek(size)
        f.write(str(random.random()))

    if time:
        time = datetime.strptime(time, '%Y-%m-%d %H:%M').timestamp()
        os.utime(str(p), (time, time))

@pytest.fixture(scope='session', autouse=True)
def tmp_target_dir(tmpdir_factory):
    katal.ARGS = MagicMock()
    tmpdir = tmpdir_factory.mktemp('katal')
    katal.ARGS.targetpath = tmpdir

    populate(tmpdir, 'a.1', size=1024**2)
    populate(tmpdir, 'b.2', time='2016-01-24 12:34')
    populate(tmpdir, 'c.3', time='2016-01-24 13:02')
    populate(tmpdir, 'd.4')

    return tmpdir

@pytest.fixture(autouse=True)
def conf():
    args = '--verbosity none'.split()

    conf = katal.Config()
    katal.CONFIG = conf
    katal.ARGS = conf
    katal.CFG_PARAMETERS = conf
    conf.read_command_line_arguments(args)
    conf.read_dict(conf.default_config())
    conf.read_dict(conf.arguments_to_dict())

    return conf

def pwd_path(filename):
    return os.path.join(os.path.abspath(os.path.curdir), filename)

def initialization(tmp_target_dir):
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

def test_select1(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'name': '.*'},
                    'target': {'name of the target files': '%fs.%e', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('as.1', 'bs.2', 'cs.3', 'ds.4')}

def test_select2(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'name': '.*2$'},
                    'target': {'name of the target files': '%ne', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('b.2',)}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('b.2e',)}

def test_select3(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'size': '<=1kB'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('b.2', 'c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('b.2', 'c.3', 'd.4')}

def test_select3(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'size': '<=1kB', 'date': '>=2016-01-24 13:00'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('c.3', 'd.4')}

def test_select4(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'size': '<=1kB', 'date': '>=2016-02'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('d.4',)}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('d.4',)}

def test_select5(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'date': '<=2016-02'},
                    'target': {'name of the target files': '%Y-%d(%m)-%f', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('b.2', 'c.3')}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('2016-01-b', '2016-01-c')}

def test_select6(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {'external program': 'false'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == set()
    assert {e.targetname for e in katal.SELECT} == set()

def test_subdir1(tmp_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(tmp_target_dir)},
                    'source.filter1': {},
                    'target': {'name of the target files': '%Y/%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {tmp_target_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {pwd_path(f) for f in ('2016/a.1', '2016/b.2', '2016/c.3', '2016/d.4')}

