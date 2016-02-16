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

import os
import copy
from datetime import datetime
import filecmp
import random
import sqlite3

import pytest

from katal import katal

@pytest.fixture
def src_dir(tmpdir):
    src_dir = tmpdir.mkdir('source')

    populate(src_dir, 'a.1', size=1024**2)
    populate(src_dir, 'b.2', time='2016-01-24 12:34')
    populate(src_dir, 'c.3', time='2016-01-24 13:02')
    populate(src_dir, 'd.4')

    return src_dir

@pytest.fixture
def src_dir_subdir(tmpdir):
    src_dir = tmpdir.mkdir('source')

    populate(src_dir, 'A/a.1', size=1024**2)
    populate(src_dir, 'A/b.2', time='2016-01-24 12:34')
    populate(src_dir, 'B/c.3', time='2016-01-24 13:02')
    populate(src_dir, 'd.4')

    return src_dir

@pytest.fixture
def target_dir(tmpdir):
    """
    Like src_dir, but scope is not session.
    Useful when files are moved or deleted.
    """
    target_dir = tmpdir.mkdir('target')
    return target_dir

@pytest.fixture
def new_target_dir(tmpdir):
    """
    Like src_dir, but scope is not session.
    Useful when files are moved or deleted.
    """
    target_dir = tmpdir.mkdir('new_target')
    return target_dir


@pytest.fixture(autouse=True)
def conf():
    args = '--verbosity none'.split()

    conf = katal.Config()
    katal.CONFIG = katal.ARGS = katal.CFG_PARAMETERS = conf
    conf.read_command_line_arguments(args)
    conf.read_dict(conf.default_config())
    conf.read_dict(conf.arguments_to_dict())

    assert conf is katal.CONFIG
    assert conf is katal.ARGS

    return conf

def read_db(config, target=None):
    katal.ARGS = katal.CONFIG = katal.CFG_PARAMETERS = config
    name = katal.get_database_fullname(target)

    con = sqlite3.Connection(name)
    con.row_factory = sqlite3.Row
    c = con.cursor()
    c.execute('SELECT * FROM dbfiles')
    l = c.fetchall()
    con.close()

    return l

def populate(path, name, time=None, size=0):
    p = path.join(name)
    if not os.path.exists(p.dirname):
        os.makedirs(p.dirname)
    # Random, else every file has the same hashid
    with p.open('w') as f:
        f.seek(size)
        f.write(str(random.random()))

    if time:
        time = datetime.strptime(time, '%Y-%m-%d %H:%M').timestamp()
        os.utime(str(p), (time, time))


def initialization(src_dir):
    args = '-cfg tests/cfgfile1.ini'.split()

    try:
        katal.main(args)
    except SystemExit as system_exit:
        assert not system_exit.code


    path = src_dir.join(katal.CST__KATALSYS_SUBDIR)
    for p in ['', katal.CST__LOG_SUBSUBDIR, katal.CST__TRASH_SUBSUBDIR,
              katal.CST__TASKS_SUBSUBDIR]:

        assert path.join(p).ensure(dir=True)

    assert path.join(katal.get_logfile_fullname()).ensure()

def test_select1(src_dir, target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'name': '.*'},
                    'target': {'name of the target files': '%fs.%e', 'tags': ''}})
    conf.targetpath = str(target_dir)

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('as.1', 'bs.2', 'cs.3', 'ds.4')}

def test_select2(src_dir, target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'name': '.*2$'},
                    'target': {'name of the target files': '%ne', 'tags': ''}})
    conf.targetpath = str(target_dir)

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('b.2',)}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('b.2e',)}

def test_select3(src_dir, target_dir, conf):
    conf.targetpath = str(target_dir)
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'size': '<=1kB'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('b.2', 'c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('b.2', 'c.3', 'd.4')}

def test_select3(src_dir, target_dir, conf):
    conf.targetpath = str(target_dir)
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'size': '<=1kB', 'date': '>=2016-01-24 13:00'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('c.3', 'd.4')}

def test_select4(src_dir, target_dir, conf):
    conf.targetpath = str(target_dir)
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'size': '<=1kB', 'date': '>=2016-02'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('d.4',)}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('d.4',)}

def test_select5(src_dir, target_dir, conf):
    conf.targetpath = str(target_dir)
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'date': '<=2016-02'},
                    'target': {'name of the target files': '%Y-%d(%m)-%f', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('b.2', 'c.3')}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('2016-01-b', '2016-01-c')}

def test_select6(src_dir, target_dir, conf):
    conf.targetpath = str(target_dir)
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {'external program': 'false'},
                    'target': {'name of the target files': '%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == set()
    assert {e.targetname for e in katal.SELECT} == set()

def test_subdir1(src_dir, target_dir, conf):
    conf.targetpath = str(target_dir)
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {},
                    'target': {'name of the target files': '%Y/%n', 'tags': ''}})

    katal.read_filters()
    katal.fill_select()

    assert {e.srcname for e in katal.SELECT} == {src_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert {e.targetname for e in katal.SELECT} == {target_dir.join(f) for f in ('2016/a.1', '2016/b.2', '2016/c.3', '2016/d.4')}

def test_copy(src_dir, target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {},
                    'target': {'name of the target files': '%n', 'tags': '', 'mode': 'copy'}})

    conf.targetpath = str(target_dir)

    katal.read_target_db()
    katal.read_filters()
    katal.fill_select()
    katal.action__add()

    # Test if the db has been created
    assert target_dir.join(katal.CST__KATALSYS_SUBDIR, katal.CST__DATABASE_NAME).isfile()

    list_target_files = []
    for dirpath, _, filenames in os.walk(str(target_dir)):
        list_target_files.extend(os.path.join(dirpath, f) for f in filenames
                                 if '.katal' not in dirpath)

    assert set(list_target_files) == {(target_dir.join(f)) for f in ('a.1', 'b.2', 'c.3', 'd.4')}

    db = read_db(conf)
    list_src_names = {row['sourcename'] for row in db}
    list_target_names = {row['targetname'] for row in db}
    list_hashid = {row['hashid'] for row in db}

    assert list_src_names == {src_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert list_target_names == {target_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert list_hashid == {katal.hashfile64(f) for f in list_target_names}

    # files are equals
    assert all(filecmp.cmp(str(target_dir.join(f)), str(src_dir.join(f)))
               for f in ('a.1', 'b.2', 'c.3', 'd.4'))

def test_move(src_dir, target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {},
                    'target': {'name of the target files': 's%n', 'tags': '', 'mode': 'move'}})

    conf.targetpath = str(target_dir)

    katal.read_target_db()
    katal.read_filters()
    katal.fill_select()
    katal.action__add()

    assert target_dir.join(katal.CST__KATALSYS_SUBDIR, katal.CST__DATABASE_NAME).isfile()

    list_target_files = []
    for dirpath, _, filenames in os.walk(str(target_dir)):
        list_target_files.extend(os.path.join(dirpath, f) for f in filenames
                                 if '.katal' not in dirpath)

    assert set(list_target_files) == {(target_dir.join(f)) for f in ('sa.1', 'sb.2', 'sc.3', 'sd.4')}

    # all files well moved
    assert src_dir.listdir() == []

    db = read_db(conf)
    list_src_names = {row['sourcename'] for row in db}
    list_target_names = {row['targetname'] for row in db}
    list_hashid = {row['hashid'] for row in db}

    assert list_src_names == {src_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert list_target_names == {target_dir.join(f) for f in ('sa.1', 'sb.2', 'sc.3', 'sd.4')}
    assert list_hashid == {katal.hashfile64(f) for f in list_target_names}

def test_rebase(src_dir, target_dir, new_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir)},
                    'source.filter1': {},
                    'target': {'name of the target files': '%n', 'tags': '', 'mode': 'copy'}})

    conf.targetpath = str(target_dir)

    # Filling the db
    katal.read_target_db()
    katal.read_filters()
    katal.fill_select()
    katal.action__add()
    katal.action__new(str(new_target_dir))

    # Warning : deep copy is not possible. So when modifying target,
    # config['target'] is modified too.
    new_conf = copy.copy(conf)
    new_conf.read_dict({'target': {'name of the target files': '%Y-%n'}})

    files, anomalies =  katal.action__rebase__files(str(new_target_dir), new_conf)
    assert not anomalies

    new_db = katal.get_database_fullname(str(new_target_dir))

    katal.action__rebase__write(str(new_db), files)

    assert new_target_dir.join(katal.CST__KATALSYS_SUBDIR, katal.CST__DATABASE_NAME).isfile()

    list_target_files = []
    for dirpath, _, filenames in os.walk(str(new_target_dir)):
        list_target_files.extend(os.path.join(dirpath, f) for f in filenames
                                 if '.katal' not in dirpath)

    assert set(list_target_files) == {(new_target_dir.join(f)) for f in ('2016-a.1', '2016-b.2', '2016-c.3', '2016-d.4')}

    db = read_db(conf, str(new_target_dir))
    list_src_names = {row['sourcename'] for row in db}
    list_target_names = {row['targetname'] for row in db}
    list_hashid = {row['hashid'] for row in db}

    assert list_src_names == {target_dir.join(f) for f in ('a.1', 'b.2', 'c.3', 'd.4')}
    assert list_target_names == {new_target_dir.join(f) for f in ('2016-a.1', '2016-b.2', '2016-c.3', '2016-d.4')}
    assert list_hashid == {katal.hashfile64(f) for f in list_target_names}
def test_rebase_subdir(src_dir_subdir, target_dir, new_target_dir, conf):
    conf.read_dict({'source': {'eval': 'filter1', 'path': str(src_dir_subdir)},
                    'source.filter1': {},
                    'target': {'name of the target files': '%n', 'tags': '', 'mode': 'copy'}})

    conf.targetpath = str(target_dir)

    katal.read_target_db()
    katal.read_filters()
    katal.fill_select()
    katal.action__add()

    # Test if the db has been created
    assert target_dir.join(katal.CST__KATALSYS_SUBDIR, katal.CST__DATABASE_NAME).isfile()

    list_target_files = []
    for dirpath, _, filenames in os.walk(str(target_dir)):
        list_target_files.extend(os.path.join(dirpath, f) for f in filenames if '.katal' not in dirpath)

    assert set(list_target_files) == {(target_dir.join(f)) for f in ('A/a.1', 'A/b.2', 'B/c.3', 'd.4')}


    #.............................
    # Rebase

    # Filling the db
    katal.action__new(str(new_target_dir))

    # Warning : deep copy is not possible. So when modifying target,
    # config['target'] is modified too.
    new_conf = copy.copy(conf)
    new_conf.read_dict({'target': {'name of the target files': '%Y/%r/%f'}})

    files, anomalies =  katal.action__rebase__files(str(new_target_dir), new_conf)
    assert not anomalies

    new_db = katal.get_database_fullname(str(new_target_dir))

    katal.action__rebase__write(str(new_db), files)

    assert new_target_dir.join(katal.CST__KATALSYS_SUBDIR, katal.CST__DATABASE_NAME).isfile()

    list_target_files = []
    for dirpath, _, filenames in os.walk(str(new_target_dir)):
        list_target_files.extend(os.path.join(dirpath, f) for f in filenames
                                 if '.katal' not in dirpath)

    assert set(list_target_files) == {(new_target_dir.join(f)) for f in ('2016/A/a', '2016/A/b', '2016/B/c', '2016/d')}

    db = read_db(conf, str(new_target_dir))
    list_src_names = {row['sourcename'] for row in db}
    list_target_names = {row['targetname'] for row in db}
    list_hashid = {row['hashid'] for row in db}

    assert list_src_names == {target_dir.join(f) for f in ('A/a.1', 'A/b.2', 'B/c.3', 'd.4')}
    assert list_hashid == {katal.hashfile64(f) for f in list_target_names}
