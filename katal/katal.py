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

        A (Python3/GPLv3/OSX-Linux-Windows/CLI) project, using no additional
        modules than the ones installed with Python3.
        ________________________________________________________________________

        Read a directory, select some files according to a configuration file
        (leaving aside the duplicates), copy the selected files in a target
        directory.
        Once the target directory is filled with some files, a database is added
        to the directory to avoid future duplicates. You can add new files to
        the target directory by using Katal one more time, with a different
        source directory.
        ________________________________________________________________________

        see README.md for more documentation.
"""
import argparse
from base64 import b64encode
from collections import namedtuple
import configparser
import ctypes
import hashlib
from datetime import datetime
import filecmp
import fnmatch
import itertools
import os
import platform
import re
import shutil
import sqlite3
import urllib.request
import sys
import unicodedata

#===============================================================================
# project's settings
#
# o for __version__ format string, see https://www.python.org/dev/peps/pep-0440/ :
#   e.g. "0.1.2.dev1" or "0.1a"
#
# o See also https://pypi.python.org/pypi?%3Aaction=list_classifiers
#
#===============================================================================
__projectname__ = "Katal"
__version__ = "0.3.3a"
__laststableversion__ = "0.3.2"  # when modifying this line, do not forget to launch fill_README.py
__author__ = "Xavier Faure (suizokukan / 94.23.197.37)"
__copyright__ = "Copyright 2015, suizokukan"
__license__ = "GPL-3.0"
__licensepypi__ = 'License :: OSI Approved :: GNU General Public License v3 (GPLv3)'
__maintainer__ = "Xavier Faure (suizokukan)"
__email__ = "suizokukan @T orange D@T fr"
__status__ = "Beta"
__statuspypi__ = 'Development Status :: 5 - Production/Stable'

#===============================================================================
# global variables
#===============================================================================

ARGS = None  # parameters given on the command line; initialized by main();

CFG_PARAMETERS = None  # see documentation:configuration file
                       # parameters read from the configuration file.
                       # see the read_parameters_from_cfgfile() function

INFOS_ABOUT_SRC_PATH = (None, None, None)  # initialized by show_infos_about_source_path()
                                           # ((int)total_size, (int)files_number, (dict)extensions)

TARGET_DB = dict()      # see documentation:database; initialized by read_target_db()

USE_LOGFILE = False     # (bool) initialized from the configuration file
LOGFILE = None          # the file descriptor, initialized by logfile_opening()
LOGFILE_SIZE = 0        # size of the current logfile.

SELECT = {}               # see documentation:selection; initialized by action__select()
SELECT_SIZE_IN_BYTES = 0  # initialized by action__select()
FILTERS = {}              # see documentation:selection; initialized by read_filters()

#===============================================================================
# type(s)
#===============================================================================

# SELECT is made of SELECTELEMENT objects, where data about the original files
# are stored.
#
# Due to Pylint's requirements, we can't name this type SelectElement.
SELECTELEMENT = namedtuple('SELECTELEMENT', ["fullname",
                                             "partialhashid",
                                             "path",
                                             "filename_no_extens",
                                             "extension",
                                             "size",
                                             "date",
                                             "targetname",
                                             "targettags",])

#===============================================================================
# global constants : CST__*
#===============================================================================

# this minimal subset of characters are the only characters to be used in the
# eval() function. Other characters are forbidden to avoid malicious code execution.
# keywords an symbols : filter, parentheses, "and", "or", "not", "xor", "True", "False"
#                       space, &, |, ^, (, ), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9
CST__AUTHORIZED_EVALCHARS = " TFasdlfiteruxnot0123456789&|^()"

CST__DATABASE_NAME = "katal.db"

CST__DEFAULT_CONFIGFILE_NAME = "katal.ini"

CST__DEFAULTCFGFILE_URL = \
        "https://raw.githubusercontent.com/suizokukan/katal/master/katal/katal.ini"

# date's string format used by Katal :
CST__DTIME_FORMAT = "%Y-%m-%d %H:%M"  # e.g. "2015-09-17 20:01"

# let's compute the length of such a string :
CST__DTIME_FORMAT_LENGTH = len(datetime.strftime(datetime.now(), CST__DTIME_FORMAT))

# when the program verifies that there's enough free space on disk, it multiplies
# the required amount of space by these coefficient
CST__FREESPACE_MARGIN = 1.1

CST__KATALSYS_SUBDIR = ".katal"

CST__LOG_SUBSUBDIR = "logs"

CST__LOGFILE_DTIMEFORMATSTR = "%Y_%m_%d__%H%M%S__%f"  # constant of the time format added to old
                                                      # logfiles' filename .
                                                      # see the backup_logfile() function .

# suffix, multiple :
# about the multiples of bytes, see e.g. https://en.wikipedia.org/wiki/Megabyte
CST__MULTIPLES = (("kB", 1000),
                  ("KB", 1000),
                  ("MB", 1000**2),
                  ("GB", 1000**3),
                  ("TB", 1000**4),
                  ("PB", 1000**5),
                  ("EB", 1000**6),
                  ("ZB", 1000**7),
                  ("YB", 1000**8),
                  ("KiB", 1024),
                  ("MiB", 1024**2),
                  ("GiB", 1024**3),
                  ("TiB", 1024**4),
                  ("PiB", 1024**5),
                  ("EiB", 1024**6),
                  ("ZiB", 1024**7),
                  ("YiB", 1024**8))

# How many bytes have to be read to compute the partial hashid ?
# See the thefilehastobeadded__db() and the hashfile64() functions.
CST__PARTIALHASHID_BYTESNBR = 1000000

# string used to create the database :
CST__SQL__CREATE_DB = 'CREATE TABLE dbfiles (' \
                      'hashid varchar(44) PRIMARY KEY UNIQUE, ' \
                      'partialhashid varchar(44), ' \
                      'size INTEGER, ' \
                      'name TEXT UNIQUE, ' \
                      'sourcename TEXT, sourcedate INTEGER, tagsstr TEXT)'

CST__TAG_SEPARATOR = ";"  # symbol used in the database between two tags.

CST__TASKS_SUBSUBDIR = "tasks"

CST__TRASH_SUBSUBDIR = "trash"

# foreground colors :
# (for more colors, see https://en.wikipedia.org/wiki/ANSI_escape_code)
CST__LINUXCONSOLECOLORS = {
    "default"       : "\033[0m",
    "red"           : "\033[0;31;1m",
    "cyan"          : "\033[0;36;1m",
    "white"         : "\033[0;37;1m",
}

# 'Linux', 'Windows', 'Java' according to https://docs.python.org/3.5/library/platform.html
CST__PLATFORM = platform.system()

################################################################################
class KatalError(BaseException):
    """
        KatalError class

        A very basic class called when an error is raised by the program.
    """
    #///////////////////////////////////////////////////////////////////////////
    def __init__(self, value):
        BaseException.__init__(self)
        self.value = value
    #///////////////////////////////////////////////////////////////////////////
    def __str__(self):
        return repr(self.value)

#///////////////////////////////////////////////////////////////////////////////
def action__add():
    """
        action__add()
        ________________________________________________________________________

        Add the source files described in SELECT/SELECT_SIZE_IN_BYTES to the
        target path.
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                (int) 0 if success, -1 if an error occured.
    """
    msg("  = copying data =")

    db_connection = sqlite3.connect(get_database_fullname())
    db_cursor = db_connection.cursor()

    if get_disk_free_space(ARGS.targetpath) < SELECT_SIZE_IN_BYTES*CST__FREESPACE_MARGIN:
        msg("    ! Not enough space on disk. Stopping the program.",
            _consolecolor="red")
        # returned value : -1 = error
        return -1

    files_to_be_added = []
    len_select = len(SELECT)
    for index, hashid in enumerate(SELECT):

        complete_source_filename = SELECT[hashid].fullname
        target_name = os.path.join(normpath(ARGS.targetpath), SELECT[hashid].targetname)

        sourcedate = datetime.utcfromtimestamp(os.path.getmtime(complete_source_filename))
        sourcedate = sourcedate.replace(second=0, microsecond=0)

        # converting the datetime object in epoch value (=the number of seconds from 1970-01-01 :
        sourcedate -= datetime(1970, 1, 1)
        sourcedate = sourcedate.total_seconds()

        if not ARGS.off:
            if CFG_PARAMETERS["target"]["mode"] == "nocopy":
                # nothing to do
                msg("    ... ({0}/{1}) due to the mode=nocopy' option, " \
                    "\"{2}\" will be simply added " \
                    "in the target database.".format(index+1, len_select,
                                                     complete_source_filename))

            elif CFG_PARAMETERS["target"]["mode"] == "copy":
                # copying the file :
                msg("    ... ({0}/{1}) about to " \
                    "copy \"{2}\" to \"{3}\" .".format(index+1,
                                                       len_select,
                                                       complete_source_filename,
                                                       target_name))
                shutil.copyfile(complete_source_filename, target_name)
                os.utime(target_name, (sourcedate, sourcedate))

            elif CFG_PARAMETERS["target"]["mode"] == "move":
                # moving the file :
                msg("    ... ({0}/{1}) about to " \
                    "move \"{2}\" to \"{3}\" .".format(index+1,
                                                       len_select,
                                                       complete_source_filename,
                                                       target_name))
                shutil.move(complete_source_filename, target_name)
                os.utime(target_name, (sourcedate, sourcedate))

        files_to_be_added.append((hashid,
                                  SELECT[hashid].partialhashid,
                                  SELECT[hashid].size,
                                  SELECT[hashid].targetname,
                                  complete_source_filename,
                                  sourcedate,
                                  SELECT[hashid].targettags))

    msg("    = all files have been copied, let's update the database... =")

    try:
        if not ARGS.off:
            db_cursor.executemany('INSERT INTO dbfiles VALUES (?,?,?,?,?,?,?)', files_to_be_added)

    except sqlite3.IntegrityError as exception:
        msg("!!! An error occured while writing the database : "+str(exception),
            _consolecolor="red")
        msg("!!! files_to_be_added : ",
            _consolecolor="red")
        for file_to_be_added in files_to_be_added:
            msg("     ! hashid={0}; partialhashid={1}; size={2}; name={3}; sourcename={4}; " \
                "sourcedate={5}; tagsstr={6}".format(*file_to_be_added),
                _consolecolor="red")
        raise KatalError("An error occured while writing the database : "+str(exception))

    db_connection.commit()
    db_connection.close()

    msg("    = ... database updated =")

    # returned value : 0 = success
    return 0

#///////////////////////////////////////////////////////////////////////////////
def action__addtag(_tag, _to):
    """
        action__addtag()
        ________________________________________________________________________

        Add a tag to the files given by the _to parameter.
        ________________________________________________________________________

        PARAMETERS
                o _tag          : (str) new tag to be added
                o _to           : (str) a regex string describing what files are
                                  concerned
    """
    msg("  = let's add the tag string \"{0}\" to {1}".format(_tag, _to))
    modify_the_tag_of_some_files(_tag=_tag, _to=_to, _mode="append")

#///////////////////////////////////////////////////////////////////////////////
def action__cleandbrm():
    """
        action__cleandbrm()
        ________________________________________________________________________

        Remove from the database the missing files, i.e. the files that do not
        exist in the target directory.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    msg("  = clean the database : remove missing files from the target directory =")

    if not os.path.exists(normpath(get_database_fullname())):
        msg("    ! no database found.",
            _consolecolor="red")
        return

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    files_to_be_rmved_from_the_db = []  # hashid of the files
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        if not os.path.exists(os.path.join(normpath(ARGS.targetpath), db_record["name"])):
            files_to_be_rmved_from_the_db.append(db_record["hashid"])
            msg("    o about to remove \"{0}\" " \
                "from the database".format(os.path.join(normpath(ARGS.targetpath),
                                                        db_record["name"])))

    if len(files_to_be_rmved_from_the_db) == 0:
        msg("    * no file to be removed : the database is ok.",
            _consolecolor="red")
    else:
        for hashid in files_to_be_rmved_from_the_db:
            if not ARGS.off:
                msg("    o removing \"{0}\" record " \
                    "from the database".format(hashid))
                db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))
                db_connection.commit()

    db_connection.close()
    if not ARGS.off:
        msg("    o ... done : removed {0} " \
            "file(s) from the database".format(len(files_to_be_rmved_from_the_db)))

#///////////////////////////////////////////////////////////////////////////////
def action__downloadefaultcfg(_targetname=CST__DEFAULT_CONFIGFILE_NAME, _location="local"):
    """
        action__downloadefaultcfg()
        ________________________________________________________________________

        Download the default configuration file; save it in the current directory
        (_location='local') or in the user's HOME directory (_location='home').
        ________________________________________________________________________

        PARAMETERS :
            o (str) _targetname : the new name of the downloaded file
            o (str) _location : "local" or "home"

        RETURNED VALUE :
            (bool) success
    """
    msg("  = downloading the default configuration file =")
    msg("    ... trying to download {0} from {1}".format(_targetname, CST__DEFAULTCFGFILE_URL))

    try:
        if not ARGS.off:
            with urllib.request.urlopen(CST__DEFAULTCFGFILE_URL) as response, \
                 open(_targetname, 'wb') as out_file:
                shutil.copyfileobj(response, out_file)
        msg("  * download completed : \"{0}\" (path : \"{1}\")".format(_targetname,
                                                                       normpath(_targetname)))

        if _location == 'home':
            newname = os.path.join(possible_paths_to_cfg()[-1],
                                   os.path.basename(_targetname))
            msg("  * Since you wrote '--downloaddefaultcfg=home', " \
                "let's move the download file to the user's home directory...")
            msg("    namely {0} -> {1}".format(_targetname, newname))
            shutil.move(_targetname, newname)

        return True

    except urllib.error.URLError as exception:
        msg("  ! An error occured : "+str(exception),
            _consolecolor="red")
        msg("  ... if you can't download the default config file, what about simply",
            _consolecolor="red")
        msg("  ... copy another config file to the target directory ?",
            _consolecolor="red")
        msg("  ... In a target directory, the config file is " \
            "in the \"{0}\" directory.".format(os.path.join(CST__KATALSYS_SUBDIR)),
            _consolecolor="red")
        return False

#///////////////////////////////////////////////////////////////////////////////
def action__findtag(_tag):
    """
        action__findtag()
        ________________________________________________________________________

        Display the files tagged with _tag. _tag is a simple string, not a
        regex. The function searches a substring _tag in the tags' string.

        With --copyto, copy the selected files into the directory whose name
        is given by ARGS.copyto .
        ________________________________________________________________________

        PARAMETER
            o _tag : (str)the searched tag

        no RETURNED VALUE
    """
    msg("  = searching the files with the tag \"{0}\" =".format(_tag))

    if not os.path.exists(normpath(get_database_fullname())):
        msg("    ! no database found.",
            _consolecolor="red")
        return

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    res = []
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        if _tag in db_record["tagsstr"]:

            res.append(db_record["name"])
            msg("    o \"{0}\" : \"{1}\"".format(db_record["name"],
                                                 tagsstr_repr(db_record["tagsstr"])))

    len_res = len(res)
    if len_res == 0:
        msg("    o no file matches the tag \"{0}\" .".format(_tag))
    elif len_res == 1:
        msg("    o one file matches the tag \"{0}\" .".format(_tag))
    else:
        msg("    o {0} files match the tag \"{1}\" .".format(len_res, _tag))

    db_connection.commit()
    db_connection.close()

    # --copyto argument :
    if ARGS.copyto:
        msg("    o copying the files into \"{0}\" (path: \"{1}\")".format(ARGS.copyto,
                                                                          normpath(ARGS.copyto)))

        if not os.path.exists(normpath(ARGS.copyto)):
            msg("    * let's create \"{0}\" (path: \"{1}\"".format(ARGS.copyto,
                                                                   normpath(ARGS.copyto)))
            if not ARGS.off:
                os.mkdir(normpath(ARGS.copyto))

        for i, filename in enumerate(res):
            src = os.path.join(normpath(ARGS.targetpath), filename)
            dest = os.path.join(normpath(ARGS.copyto), filename)
            msg("    o ({0}/{1}) copying \"{2}\" as \"{3}\"...".format(i+1, len_res, src, dest))
            if not ARGS.off:
                shutil.copy(src, dest)

#///////////////////////////////////////////////////////////////////////////////
def action__infos():
    """
        action__infos()
        ________________________________________________________________________

        Display informations about the source and the target directory
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                (int) 0 if ok, -1 if an error occured
    """
    msg("  = informations =")
    show_infos_about_source_path()
    return show_infos_about_target_path()

#///////////////////////////////////////////////////////////////////////////////
def action__new(_targetname):
    """
        action__new()
        ________________________________________________________________________

        Create a new target directory
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    msg("  = about to create a new target directory " \
        "named \"{0}\" (path : \"{1}\")".format(_targetname,
                                                normpath(_targetname)))
    if os.path.exists(normpath(_targetname)):
        msg("  ! can't go further : the directory already exists.",
            _consolecolor="red")
        return

    if not ARGS.off:
        msg("  ... creating the target directory with its sub-directories...")
        os.mkdir(normpath(_targetname))
        os.mkdir(os.path.join(normpath(_targetname), CST__KATALSYS_SUBDIR))
        os.mkdir(os.path.join(normpath(_targetname), CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR))
        os.mkdir(os.path.join(normpath(_targetname), CST__KATALSYS_SUBDIR, CST__TASKS_SUBSUBDIR))
        os.mkdir(os.path.join(normpath(_targetname), CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR))

        create_empty_db(os.path.join(normpath(_targetname),
                                     CST__KATALSYS_SUBDIR,
                                     CST__DATABASE_NAME))

    if ARGS.verbosity != 'none':
        answer = \
            input("\nDo you want to download the default config file " \
                  "into the expected directory ? (y/N) ")

        if answer in ("y", "yes"):
            res = action__downloadefaultcfg(_targetname=os.path.join(normpath(_targetname),
                                                                     CST__KATALSYS_SUBDIR,
                                                                     CST__DEFAULT_CONFIGFILE_NAME),
                                            _location="local")
            if not res:
                msg("  ! A problem occured : " \
                    "the creation of the target directory has been aborted.",
                    _consolecolor="red")

    msg("  ... done with the creation of \"{0}\" as a new target directory.".format(_targetname))

#///////////////////////////////////////////////////////////////////////////////
def action__rebase(_newtargetpath):
    """
        action__rebase()
        ________________________________________________________________________

        Copy the current target directory into a new one, modifying the filenames.
        ________________________________________________________________________

        PARAMETER :
                o _newtargetpath        : (str) path to the new target directory.

        no RETURNED VALUE
    """
    source_path = CFG_PARAMETERS["source"]["path"]

    msg("  = copying the current target directory into a new one =")
    msg("    o from {0} (path : \"{1}\")".format(source_path,
                                                 normpath(source_path)))

    msg("    o to   {0} (path : \"{1}\")".format(_newtargetpath,
                                                 normpath(_newtargetpath)))

    to_configfile = os.path.join(_newtargetpath,
                                 CST__KATALSYS_SUBDIR,
                                 CST__DEFAULT_CONFIGFILE_NAME)
    msg("    o trying to read dest config file {0} " \
        "(path : \"{1}\") .".format(to_configfile,
                                    normpath(to_configfile)))
    dest_params = read_parameters_from_cfgfile(normpath(to_configfile))

    if dest_params is None:
        msg("    ! can't read the dest config file !",
            _consolecolor="red")
        return

    msg("    o config file found and read (ok)")
    msg("    o new filenames' format : " \
        "{0}".format(dest_params["target"]["name of the target files"]))
    msg("    o tags to be added : " \
        "{0}".format(dest_params["target"]["tags"]))

    new_db = os.path.join(normpath(_newtargetpath), CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)
    if not ARGS.off:
        if os.path.exists(new_db):
            # let's delete the previous new database :
            os.remove(new_db)

    # let's compute the new names :
    olddb_connection = sqlite3.connect(get_database_fullname())
    olddb_connection.row_factory = sqlite3.Row
    olddb_cursor = olddb_connection.cursor()

    files, anomalies_nbr = action__rebase__files(olddb_cursor, dest_params, _newtargetpath)

    go_on = True
    if anomalies_nbr != 0:
        go_on = False
        answer = \
            input("\nAt least one anomaly detected (see details above) " \
                  "Are you sure you want to go on ? (y/N) ")

        if answer in ("y", "yes"):
            go_on = True

    if not go_on:
        olddb_connection.close()
        return
    else:
        action__rebase__write(new_db, files)
        olddb_connection.close()

#///////////////////////////////////////////////////////////////////////////////
def action__rebase__files(_olddb_cursor, _dest_params, _newtargetpath):
    """
        action__rebase__files()
        ________________________________________________________________________

        Return a dict of the files to be copied (old name, new name, ...) and
        the number of anomalies.

        Anomalies : files' names collisions.
        ________________________________________________________________________

        PARAMETER :
                o _olddb_cursor         : cursor to the source database
                o _dest_params          : an object returned by read_parameters_from_cfgfile(),
                                          like CFG_PARAMETERS
                o _newtargetpath        : (str) path to the new target directory.

        RETURNED VALUE :
                (files, (int)number of anomalies)

                files : a dict hashid::( (0)source name,
                                         (1)new name,
                                         (2)source date,
                                         (3)source tagsstr,
                                         (4)size,
                                         (5)partialhashid)
    """
    source_path = CFG_PARAMETERS["source"]["path"]

    files = dict()      # dict to be returned.
    filenames = set()   # to be used to avoid duplicates.

    anomalies_nbr = 0
    for index, olddb_record in enumerate(_olddb_cursor.execute('SELECT * FROM dbfiles')):
        fullname = normpath(os.path.join(source_path, olddb_record["name"]))
        filename_no_extens, extension = get_filename_and_extension(fullname)

        size = olddb_record["size"]
        date = olddb_record["sourcedate"]
        new_name = \
            create_target_name(_parameters=_dest_params,
                               _hashid=olddb_record["hashid"],
                               _filename_no_extens=filename_no_extens,
                               _path=olddb_record["sourcename"],
                               _extension=extension,
                               _size=size,
                               _date=datetime.utcfromtimestamp(date).strftime(CST__DTIME_FORMAT),
                               _database_index=index)
        new_name = normpath(os.path.join(_newtargetpath, new_name))
        tagsstr = olddb_record["tagsstr"]

        msg("      o {0} : {1} would be copied as {2}".format(olddb_record["hashid"],
                                                              olddb_record["name"],
                                                              new_name))

        if new_name in filenames:
            msg("      ! anomaly : ancient file {1} should be renamed as {0} " \
                "but this name would have been already created in the new target directory ! " \
                "".format(new_name, fullname),
                _consolecolor="red")
            msg("        Two different files from the ancient target directory " \
                "can't bear the same name in the new target directory !",
                _consolecolor="red")
            anomalies_nbr += 1
        elif os.path.exists(new_name):
            msg("      ! anomaly : ancient file {1} should be renamed as {0} " \
                "but this name already exists in new target directory !".format(new_name, fullname),
                _consolecolor="red")
            anomalies_nbr += 1
        else:
            files[olddb_record["hashid"]] = (fullname, new_name, date, tagsstr)
            filenames.add(new_name)

    return files, anomalies_nbr

#///////////////////////////////////////////////////////////////////////////////
def action__rebase__write(_new_db, _files):
    """
        action__rebase__write()
        ________________________________________________________________________

        Write the files described by _files in the new target directory.
        ________________________________________________________________________

        PARAMETER :
                o _new_db               : (str) new database's name
                o _files                : (dict) see action__rebase__files()

        no RETURNED VALUE
    """
    # let's write the new database :
    newdb_connection = sqlite3.connect(_new_db)
    newdb_connection.row_factory = sqlite3.Row
    newdb_cursor = newdb_connection.cursor()

    try:
        if not ARGS.off:
            newdb_cursor.execute(CST__SQL__CREATE_DB)

        for index, futurefile_hashid in enumerate(_files):
            futurefile = _files[futurefile_hashid]
            file_to_be_added = (futurefile_hashid,      # hashid
                                futurefile[5],          # partial hashid
                                futurefile[4],          # size
                                futurefile[1],          # new name
                                futurefile[0],          # sourcename
                                futurefile[2],          # sourcedate
                                futurefile[3])          # tags

            strdate = datetime.utcfromtimestamp(futurefile[2]).strftime(CST__DTIME_FORMAT)
            msg("    o ({0}/{1}) adding a file in the new database".format(index+1, len(_files)))
            msg("      o hashid      : {0}".format(futurefile_hashid))
            msg("      o source name : \"{0}\"".format(futurefile[0]))
            msg("      o desti. name : \"{0}\"".format(futurefile[1]))
            msg("      o source date : {0}".format(strdate))
            msg("      o size        : {0}".format(futurefile[4]))
            msg("      o tags        : \"{0}\"".format(futurefile[3]))

            if not ARGS.off:
                newdb_cursor.execute('INSERT INTO dbfiles VALUES (?,?,?,?,?,?,?)', file_to_be_added)
                newdb_connection.commit()

    except sqlite3.IntegrityError as exception:
        msg("!!! An error occured while writing the new database : "+str(exception))
        raise KatalError("An error occured while writing the new database : "+str(exception))

    newdb_connection.close()

    # let's copy the files :
    for index, futurefile_hashid in enumerate(_files):
        futurefile = _files[futurefile_hashid]
        old_name, new_name = futurefile[0], futurefile[1]

        msg("    o ({0}/{1}) copying \"{2}\" as \"{3}\"".format(index+1, len(_files),
                                                                old_name, new_name))
        if not ARGS.off:
            shutil.copyfile(old_name, new_name)

    msg("    ... done")

#///////////////////////////////////////////////////////////////////////////////
def action__reset():
    """
        action__reset()
        ________________________________________________________________________

        Delete the files in the target directory and the database.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    msg("    = about to delete (=move in the trash) the target files and the database.")

    if not os.path.exists(normpath(get_database_fullname())):
        msg("    ! no database found, nothing to do .",
            _consolecolor="red")
        return

    if ARGS.verbosity != 'none':
        answer = \
            input("\nDo you really want to delete (=move to the katal trash directory)" \
                  "the files in the target directory and the database (y/N) ")
        if answer not in ("y", "yes"):
            return

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    files_to_be_removed = []  # a list of (hashid, fullname)
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        files_to_be_removed.append((db_record["hashid"], db_record["name"]))

    for hashid, name in files_to_be_removed:
        msg("   o removing {0} from the database and from the target path".format(name))
        if not ARGS.off:
            # let's remove the file from the target directory :
            shutil.move(os.path.join(normpath(ARGS.targetpath), name),
                        os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR, name))
            # let's remove the file from the database :
            db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))

            db_connection.commit()

    db_connection.close()

    msg("    = ... done : the database should be empty, the target files should no longer exist.")

#///////////////////////////////////////////////////////////////////////////////
def action__rmnotags():
    """
        action__rmnotags
        ________________________________________________________________________

        Remove all files (from the target directory and from the database) if
        they have no tags.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    msg("  = removing all files with no tags (=moving them to the trash) =")

    if not os.path.exists(normpath(get_database_fullname())):
        msg("    ! no database found.",
            _consolecolor="red")
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        files_to_be_removed = []    # list of (hashid, name)
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if db_record["tagsstr"] == "":
                files_to_be_removed.append((db_record["hashid"], db_record["name"]))

        if len(files_to_be_removed) == 0:
            msg("   ! no files to be removed.",
                _consolecolor="red")
        else:
            for hashid, name in files_to_be_removed:
                msg("   o removing {0} from the database and from the target path".format(name))
                if not ARGS.off:
                    # let's remove the file from the target directory :
                    shutil.move(os.path.join(normpath(ARGS.targetpath), name),
                                os.path.join(normpath(ARGS.targetpath),
                                             CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR, name))
                    # let's remove the file from the database :
                    db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))

        db_connection.commit()
        db_connection.close()

#///////////////////////////////////////////////////////////////////////////////
def action__rmtags(_to):
    """
        action__rmtags()
        ________________________________________________________________________

        Remove the tags' string(s) in the target directory, overwriting ancient tags.
        ________________________________________________________________________

        PARAMETERS
                o _to           : (str) a regex string describing what files are
                                  concerned
    """
    msg("  = let's remove the tags' string(s) in {0}".format(_to))
    action__settagsstr(_tagsstr="", _to=_to)

#///////////////////////////////////////////////////////////////////////////////
def action__select():
    """
        action__select()
        ________________________________________________________________________

        fill SELECT and SELECT_SIZE_IN_BYTES and display what's going on.
        This function will always be called before a call to action__add().
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE.
    """
    msg("  = selecting files according to the instructions " \
                "in the config file... =")

    msg("  o the files will be copied in \"{0}\" " \
        "(path: \"{1}\")".format(ARGS.targetpath,
                                 normpath(ARGS.targetpath)))
    msg("  o the files will be renamed according " \
        "to the \"{0}\" pattern.".format(CFG_PARAMETERS["target"]["name of the target files"]))

    msg("  o filters :")

    for filter_index in FILTERS:
        msg("    o filter #{0} : {1}".format(filter_index,
                                             FILTERS[filter_index]))
    msg("  o file list :")

    # let's initialize SELECT and SELECT_SIZE_IN_BYTES :
    number_of_discarded_files = fill_select()

    msg("    o size of the selected file(s) : {0}".format(size_as_str(SELECT_SIZE_IN_BYTES)))

    if len(SELECT) == 0:
        msg("    ! no file selected ! " \
            "You have to modify the config file to get some files selected.",
            _consolecolor="red")
    else:
        ratio = len(SELECT)/(len(SELECT)+number_of_discarded_files)*100.0
        msg("    o number of selected files " \
                  "(after discarding {1} file(s)) : {0}, " \
                  "{2:.2f}% of the source files.".format(len(SELECT),
                                                         number_of_discarded_files,
                                                         ratio))

    # let's check that the target path has sufficient free space :
    if CFG_PARAMETERS["target"]["mode"] != "nocopy":
        available_space = get_disk_free_space(ARGS.targetpath)
        if available_space > SELECT_SIZE_IN_BYTES*CST__FREESPACE_MARGIN:
            size_ok = "ok"
            colorconsole = "white"
        else:
            size_ok = "!!! problem !!!"
            colorconsole = "red"

        msg("    o required space : {0}; " \
            "available space on disk : {1} ({2})".format(size_as_str(SELECT_SIZE_IN_BYTES),
                                                         size_as_str(available_space),
                                                         size_ok),
            _consolecolor=colorconsole)

    # if there's no --add option, let's give some examples of the target names :
    if not ARGS.add and CFG_PARAMETERS["target"]["mode"] != "nocopy":
        example_index = 0
        for hashid in SELECT:

            complete_source_filename = SELECT[hashid].fullname

            target_name = os.path.join(normpath(ARGS.targetpath), SELECT[hashid].targetname)

            msg("    o e.g. ... \"{0}\" " \
                "would be copied as \"{1}\" .".format(complete_source_filename,
                                                      target_name))

            example_index += 1

            if example_index > 5:
                break

#///////////////////////////////////////////////////////////////////////////////
def action__settagsstr(_tagsstr, _to):
    """
        action__settagsstr()
        ________________________________________________________________________

        Set the tags' string(s) in the target directory, overwriting ancient tags.
        ________________________________________________________________________

        PARAMETERS
                o _tagsstr      : (str) the new tags' strings
                o _to           : (str) a regex string describing what files are
                                  concerned
    """
    msg("  = let's apply the tag string\"{0}\" to {1}".format(_tagsstr, _to))
    modify_the_tag_of_some_files(_tag=_tagsstr, _to=_to, _mode="set")

#///////////////////////////////////////////////////////////////////////////////
def action__target_kill(_filename):
    """
        action__target_kill()
        ________________________________________________________________________

        Delete _filename from the target directory and from the database.
        ________________________________________________________________________

        PARAMETER
                o  _filename    : (str) file's name to be deleted.
                                  DO NOT GIVE A PATH, just the file's name,
                                  without the path to the target directory

        RETURNED VALUE
                (int) : 0 if success, -1 if the file doesn't exist in the target
                        directory, -2 if the file doesn't exist in the database,
                        -3 if there's no database.
    """
    msg("  = about to remove \"{0}\" from the target directory (=file moved to the trash) " \
        "and from its database =".format(_filename))
    if not os.path.exists(os.path.join(normpath(ARGS.targetpath), _filename)):
        msg("    ! can't find \"{0}\" file on disk.".format(_filename),
            _consolecolor="red")
        return -1

    if not os.path.exists(normpath(get_database_fullname())):
        msg("    ! no database found.",
            _consolecolor="red")
        return -3
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        filename_hashid = None
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if db_record["name"] == os.path.join(normpath(ARGS.targetpath), _filename):
                filename_hashid = db_record["hashid"]

        if filename_hashid is None:
            msg("    ! can't find \"{0}\" file in the database.".format(_filename),
                _consolecolor="red")
            res = -2
        else:
            if not ARGS.off:
                # let's remove _filename from the target directory :
                shutil.move(os.path.join(normpath(ARGS.targetpath), _filename),
                            os.path.join(normpath(ARGS.targetpath),
                                         CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR, _filename))

                # let's remove _filename from the database :
                db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (filename_hashid,))

            res = 0  # success.

        db_connection.commit()
        db_connection.close()

        msg("    ... done")
        return res

#///////////////////////////////////////////////////////////////////////////////
def action__whatabout(_src):
    """
        action__whatabout()
        ________________________________________________________________________

        Take a look at the _src file/directory and answer the following question :
        is this file/(are these files) already in the target directory ?
        ________________________________________________________________________

        PARAMETER
            o _src : (str) the source file's name

        RETURNED VALUE : (bool)is everything ok (=no error) ?
    """
    #. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
    def show_infos_about_a_srcfile(_srcfile_name):
        """
                Display the expected informations about a file named _srcfile_name .
        """
        msg("  = what about the \"{0}\" file ? (path : \"{1}\")".format(_src, _srcfile_name))
        size = os.stat(_srcfile_name).st_size
        msg("    = size : {0}".format(size_as_str(size)))

        sourcedate = datetime.utcfromtimestamp(os.path.getmtime(_srcfile_name))
        sourcedate = sourcedate.replace(second=0, microsecond=0)
        sourcedate2 = sourcedate
        sourcedate2 -= datetime(1970, 1, 1)
        sourcedate2 = sourcedate2.total_seconds()
        msg("    = mtime : {0} (epoch value : {1})".format(sourcedate, sourcedate2))

        srchash = hashfile64(_srcfile_name)
        msg("    = hash : {0}".format(srchash))

        # is the hash in the database ?
        already_present_in_db = False
        for hashid in TARGET_DB:
            if hashid == srchash:
                already_present_in_db = True
                break
        if already_present_in_db:
            msg("    = the file's content is equal to a file ALREADY present in the database.")
        else:
            msg("    = the file isn't present in the database.")

    # (1) does _src exist ?
    normsrc = normpath(_src)
    if not os.path.exists(normsrc):
        msg("  ! error : can't find source file \"{0}\" .".format(normsrc),
            _consolecolor="red")
        return False

    # (2) is _src a file or a directory ?
    if os.path.isdir(normsrc):
        # informations about the source directory :
        if normpath(ARGS.targetpath) in normsrc:
            msg("  ! error : the given directory is inside the target directory.",
                _consolecolor="red")
            return False

        for dirpath, _, filenames in os.walk(normpath(_src)):
            for filename in filenames:
                fullname = os.path.join(normpath(dirpath), filename)
                show_infos_about_a_srcfile(fullname)

    else:
        # informations about the source file :
        if normpath(ARGS.targetpath) in normpath(_src):
            # special case : the file is inside the target directory :
            msg("  = what about the \"{0}\" file ? (path : \"{1}\")".format(_src, normsrc))
            msg("    This file is inside the target directory.")
            srchash = hashfile64(normsrc)
            msg("    = hash : {0}".format(srchash))
            msg("    Informations extracted from the database :")
            # informations from the database :
            db_connection = sqlite3.connect(get_database_fullname())
            db_connection.row_factory = sqlite3.Row
            db_cursor = db_connection.cursor()
            for db_record in db_cursor.execute("SELECT * FROM dbfiles WHERE hashid=?", (srchash,)):
                msg("    = partial hashid : {0}".format(db_record["partialhashid"]))
                msg("    = name : {0}".format(db_record["name"]))
                msg("    = size : {0}".format(db_record["size"]))
                msg("    = source name : {0}".format(db_record["sourcename"]))
                msg("    = source date : {0}".format(db_record["sourcedate"]))
                msg("    = tags' string : {0}".format(db_record["tagsstr"]))
            db_connection.close()

        else:
            # normal case : the file is outside the target directory :
            show_infos_about_a_srcfile(normpath(_src))

    return True

#///////////////////////////////////////////////////////////////////////////////
def add_keywords_in_targetstr(_srcstring,
                              _hashid,
                              _filename_no_extens,
                              _path,
                              _extension,
                              _size,
                              _date,
                              _database_index):
    """
        add_keywords_in_targetstr()
        ________________________________________________________________________

        The function replaces some keywords in the string by the parameters given
        to this function.
        The function returned a string which may be used to create target files.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o _parameters                   : an object returned by
                                                  read_parameters_from_cfgfile(),
                                                  like CFG_PARAMETERS
                o _hashid                       : (str)
                o _filename_no_extens           : (str)
                o _path                         : (str
                o _extension                    : (str)
                o _size                         : (int)
                o _date                         : (str) see CST__DTIME_FORMAT
                o _database_index               : (int)

        RETURNED VALUE
                (str)the expected string
    """
    res = _srcstring

    # beware : order matters !
    res = res.replace("%ht",
                      hex(int(datetime.strptime(_date,
                                                CST__DTIME_FORMAT).timestamp()))[2:])

    res = res.replace("%h", _hashid)

    res = res.replace("%ff", remove_illegal_characters(_filename_no_extens))
    res = res.replace("%f", _filename_no_extens)

    res = res.replace("%pp", remove_illegal_characters(_path))
    res = res.replace("%p", _path)

    res = res.replace("%ee", remove_illegal_characters(_extension))
    res = res.replace("%e", _extension)

    res = res.replace("%s", str(_size))

    res = res.replace("%dd", remove_illegal_characters(_date))

    res = res.replace("%t",
                      str(int(datetime.strptime(_date,
                                                CST__DTIME_FORMAT).timestamp())))

    res = res.replace("%i",
                      remove_illegal_characters(str(_database_index)))

    return res

#///////////////////////////////////////////////////////////////////////////////
def backup_logfile(_logfile_fullname):
    """
        backup_logfile()
        ________________________________________________________________________

        copy a logfile named _logfile_fullname into a backuped file.

          o  The backuped file is stored in the CST__LOG_SUBSUBDIR directory.
          o  The name of the backuped file is automatically created from a call to
             datetime.now() . See the CST__LOGFILE_DTIMEFORMATSTR constant.
        ________________________________________________________________________

        NO PARAMETER, no RETURNED VALUE
    """
    logfile_backup = os.path.join(CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR,
                                  CFG_PARAMETERS["log file"]["name"] + \
                                  datetime.strftime(datetime.now(),
                                                    CST__LOGFILE_DTIMEFORMATSTR))
    shutil.copyfile(_logfile_fullname, logfile_backup)

#///////////////////////////////////////////////////////////////////////////////
def check_args():
    """
        check_args()
        ________________________________________________________________________

        check the arguments of the command line. Raise an exception if something
        is wrong.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    # --select and --add can't be used simultaneously.
    if ARGS.add is True and ARGS.select is True:
        raise KatalError("--select and --add can't be used simultaneously")

    # --settagsstr must be used with --to :
    if ARGS.settagsstr and not ARGS.to:
        raise KatalError("please use --to in combination with --settagsstr")

    # --addtag must be used with --to :
    if ARGS.addtag and not ARGS.to:
        raise KatalError("please use --to in combination with --addtag")

    # --rmtags must be used with --to :
    if ARGS.rmtags and not ARGS.to:
        raise KatalError("please use --to in combination with --rmtags")

    # --strictcmp can only be used with --select or with --add :
    if ARGS.strictcmp and not (ARGS.add or ARGS.select):
        raise KatalError("--strictcmp can only be used in combination with --select or with --add")

    # --copyto can only be used with --findtag :
    if ARGS.copyto and not ARGS.findtag:
        raise KatalError("--copyto can only be used in combination with --findtag .")

#///////////////////////////////////////////////////////////////////////////////
def create_empty_db(_db_name):
    """
        create_empty_db()
        ________________________________________________________________________

        Create an empty database named _db_name .
        ________________________________________________________________________

        PARAMETER :
            o _db_name : name of the file to be created .
                         Please use a normpath'd parameter : the normpath function
                         will not be called by create_empty_db() !

        no RETURNED VALUE
    """
    msg("  ... creating an empty database named \"{0}\"...".format(_db_name))

    if not ARGS.off:

        db_connection = sqlite3.connect(_db_name)
        db_cursor = db_connection.cursor()

        db_cursor.execute(CST__SQL__CREATE_DB)

        db_connection.commit()
        db_connection.close()

    msg("   ... database created")

#///////////////////////////////////////////////////////////////////////////////
def create_subdirs_in_target_path():
    """
        create_subdirs_in_target_path()
        ________________________________________________________________________

        Create the expected subdirectories in ARGS.targetpath .
        ________________________________________________________________________

        no PARAMETERS, no RETURNED VALUE
    """
    # (str)name for the message, (str)full path :
    for name, \
        fullpath in (("target", ARGS.targetpath),
                     ("system", os.path.join(normpath(ARGS.targetpath),
                                             CST__KATALSYS_SUBDIR)),
                     ("trash", os.path.join(normpath(ARGS.targetpath),
                                            CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR)),
                     ("log", os.path.join(normpath(ARGS.targetpath),
                                          CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR)),
                     ("tasks", os.path.join(normpath(ARGS.targetpath),
                                            CST__KATALSYS_SUBDIR, CST__TASKS_SUBSUBDIR))):
        if not os.path.exists(normpath(fullpath)):
            msg("  * Since the {0} path \"{1}\" (path : \"{2}\") " \
                "doesn't exist, let's create it.".format(name,
                                                         fullpath,
                                                         normpath(fullpath)))
            if not ARGS.off:
                os.mkdir(normpath(fullpath))

#/////////////////////////////////////////////////////////////////////////////////////////
def create_target_name(_parameters,
                       _hashid,
                       _filename_no_extens,
                       _path,
                       _extension,
                       _size,
                       _date,
                       _database_index):
    """
        create_target_name()
        ________________________________________________________________________

        Create the name of a file (a target file) from various informations
        given by the parameters. The function reads the string stored in
        _parameters["target"]["name of the target files"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o _parameters                   : an object returned by
                                                  read_parameters_from_cfgfile(),
                                                  like CFG_PARAMETERS
                o _hashid                       : (str)
                o _filename_no_extens           : (str)
                o _path                         : (str
                o _extension                    : (str)
                o _size                         : (int)
                o _date                         : (str) see CST__DTIME_FORMAT
                o _database_index               : (int)

        RETURNED VALUE
                (str)name
    """
    return(add_keywords_in_targetstr(_srcstring=_parameters["target"]["name of the target files"],
                                     _hashid=_hashid,
                                     _filename_no_extens=_filename_no_extens,
                                     _path=_path,
                                     _extension=_extension,
                                     _size=_size,
                                     _date=_date,
                                     _database_index=_database_index))

#/////////////////////////////////////////////////////////////////////////////////////////
def create_target_name_and_tags(_parameters,
                                _hashid,
                                _filename_no_extens,
                                _path,
                                _extension,
                                _size,
                                _date,
                                _database_index):
    """
        create_target_name_and_tags()
        ________________________________________________________________________

        Create the name of a file (a target file) from various informations
        given by the parameters. The function reads the string stored in
        _parameters["target"]["name of the target files"] and in
        _parameters["target"]["tags"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o _parameters                   : an object returned by
                                                  read_parameters_from_cfgfile(),
                                                  like CFG_PARAMETERS
                o _hashid                       : (str)
                o _filename_no_extens           : (str)
                o _path                         : (str
                o _extension                    : (str)
                o _size                         : (int)
                o _date                         : (str) see CST__DTIME_FORMAT
                o _database_index               : (int)

        RETURNED VALUE
                ( (str)name, (str)tags )
    """
    name = create_target_name(_parameters,
                              _hashid,
                              _filename_no_extens,
                              _path,
                              _extension,
                              _size,
                              _date,
                              _database_index)

    tags = create_target_name(_parameters,
                              _hashid,
                              _filename_no_extens,
                              _path,
                              _extension,
                              _size,
                              _date,
                              _database_index)
    return (name, tags)

#/////////////////////////////////////////////////////////////////////////////////////////
def create_target_tags(_parameters,
                       _hashid,
                       _filename_no_extens,
                       _path,
                       _extension,
                       _size,
                       _date,
                       _database_index):
    """
        create_target_tags()
        ________________________________________________________________________

        Create the tags of a file (a target file) from various informations
        given by the parameters. The function reads the string stored in
        _parameters["target"]["tags"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o _parameters                   : an object returned by
                                                  read_parameters_from_cfgfile(),
                                                  like CFG_PARAMETERS
                o _hashid                       : (str)
                o _filename_no_extens           : (str)
                o _path                         : (str
                o _extension                    : (str)
                o _size                         : (int)
                o _date                         : (str) see CST__DTIME_FORMAT
                o _database_index               : (int)

        RETURNED VALUE
                (str)name
    """
    return(add_keywords_in_targetstr(_srcstring=_parameters["target"]["tags"],
                                     _hashid=_hashid,
                                     _filename_no_extens=_filename_no_extens,
                                     _path=_path,
                                     _extension=_extension,
                                     _size=_size,
                                     _date=_date,
                                     _database_index=_database_index))

#///////////////////////////////////////////////////////////////////////////////
def draw_table(_rows, _data):
    """
        draw_table()
        ________________________________________________________________________

        Draw a table with some <_rows> and fill it with _data. The output is
        created by calling the msg() function.
        ________________________________________________________________________

        PARAMETERS :
            o rows= ( ((str)row_name, (int)max length for this row), (str)separator)
                   e.g. :
                   rows= ( ("hashid", HASHID_MAXLENGTH, "|"), )
            o  _data : ( (str)row_content1, (str)row_content2, ...)

        no RETURNED VALUE
    """

    #...........................................................................
    def draw_line():
        " draw a simple line made of + and -"
        string = " "*6 + "+"
        for _, row_maxlength, _ in rows:
            string += "-"*(row_maxlength+2) + "+"
        msg(string)

    # real rows' widths : it may happen that a row's width is greater than
    # the maximal value given in _rows since the row name is longer than
    # this maximal value.
    rows = []
    for row_name, row_maxlength, row_separator in _rows:
        rows.append((row_name, max(len(row_name), row_maxlength), row_separator))

    # header :
    draw_line()

    string = " "*6 + "|"
    for row_name, row_maxlength, row_separator in rows:
        string += " " + row_name + " "*(row_maxlength-len(row_name)+1) + row_separator
    msg(string)

    draw_line()

    # data :
    for linedata in _data:
        string = "      |"
        for row_index, row_content in enumerate(linedata):
            text = shortstr(row_content, _rows[row_index][1])
            string += " " + \
                      text + \
                      " "*(rows[row_index][1]-len(text)) + \
                      " " + rows[row_index][2]
        msg(string)  # let's write the computed line

    draw_line()

#///////////////////////////////////////////////////////////////////////////////
def eval_filter_for_a_file(_filter, _filename, _size, _date):
    """
        eval_filter_for_a_file()
        ________________________________________________________________________

        Eval a file according to a filter and answers the following question :
        does the file matches what is described in the filter ?
        ________________________________________________________________________

        PARAMETERS
                o _filter        : a dict, see documentation:select
                o _filename     : (str) file's name
                o _size         : (int) file's size, in bytes.
                o _date         : (str)file's date

        RETURNED VALUE
                a boolean, giving the expected answer
    """
    res = True

    if res and "name" in _filter:
        res = thefilehastobeadded__filt_name(_filter, _filename)
    if res and "size" in _filter:
        res = thefilehastobeadded__filt_size(_filter, _size)
    if res and "date" in _filter:
        res = thefilehastobeadded__filt_date(_filter, _date)

    return res

#///////////////////////////////////////////////////////////////////////////////
def fill_select(_debug_datatime=None):
    """
        fill_select()
        ________________________________________________________________________

        Fill SELECT and SELECT_SIZE_IN_BYTES from the files stored in
        the source path. This function is used by action__select() .
        ________________________________________________________________________

        PARAMETERS
                o  _debug_datatime : None (normal value) or a dict of CST__DTIME_FORMAT
                                     strings if in debug/test mode.

        RETURNED VALUE
                (int) the number of discarded files
    """
    global SELECT, SELECT_SIZE_IN_BYTES

    source_path = CFG_PARAMETERS["source"]["path"]

    SELECT = {}  # see the SELECT format in the documentation:selection
    SELECT_SIZE_IN_BYTES = 0
    number_of_discarded_files = 0

    # these variables will be used by fill_select__checks() too.
    prefix = ""
    fullname = ""

    file_index = 0  # number of the current file in the source directory.
    for dirpath, _, filenames in os.walk(normpath(source_path)):
        for filename in filenames:

            # ..................................................................
            # gathering informations about filename :
            # ..................................................................
            file_index += 1
            fullname = os.path.join(normpath(dirpath), filename)

            # ..................................................................
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link on the
            #   "size = os.stat(normpath(fullname)).st_size" line (see below).
            # ..................................................................
            if os.path.exists(fullname):
                size = os.stat(normpath(fullname)).st_size
                if _debug_datatime is None:
                    time = datetime.utcfromtimestamp(os.path.getmtime(normpath(fullname)))
                    time = time.replace(second=0, microsecond=0)
                else:
                    time = datetime.strptime(_debug_datatime[fullname], CST__DTIME_FORMAT)

                fname_no_extens, extension = get_filename_and_extension(normpath(filename))

                # if we know the total amount of files to be selected (see the --infos option),
                # we can add the percentage done :
                prefix = ""
                if INFOS_ABOUT_SRC_PATH[1] is not None and INFOS_ABOUT_SRC_PATH[1] != 0:
                    prefix = "[{0:.4f}%]".format(file_index/INFOS_ABOUT_SRC_PATH[1]*100.0)

                # ..................................................................
                # what should we do with 'filename' ?
                # ..................................................................
                if not thefilehastobeadded__filters(filename, size, time):
                    # ... nothing : incompatibility with at least one filter :
                    number_of_discarded_files += 1

                    if ARGS.verbosity == 'high':
                        msg("    - {0} discarded \"{1}\" " \
                            ": incompatibility with the filter(s)".format(prefix, fullname))
                else:
                    # 'filename' being compatible with the filters, let's try
                    # to add it in the datase :
                    tobeadded, partialhashid, hashid = thefilehastobeadded__db(fullname, size)

                    if tobeadded and hashid in SELECT:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # tobeadded is True but hashid is already in SELECT; let's discard
                        # <filename> :
                        number_of_discarded_files += 1

                        if ARGS.verbosity == 'high':
                            msg("    - {0} (similar hashid among the files to be copied, " \
                                "in the source directory) " \
                                " discarded \"{1}\"".format(prefix, fullname))

                    elif tobeadded:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # ok, let's add <filename> to SELECT...
                        SELECT[hashid] = \
                         SELECTELEMENT(fullname=fullname,
                                       partialhashid=partialhashid,
                                       path=dirpath,
                                       filename_no_extens=fname_no_extens,
                                       extension=extension,
                                       size=size,
                                       date=time.strftime(CST__DTIME_FORMAT),
                                       targetname= \
                                          create_target_name(_parameters=CFG_PARAMETERS,
                                                             _hashid=hashid,
                                                             _filename_no_extens=fname_no_extens,
                                                             _path=dirpath,
                                                             _extension=extension,
                                                             _size=size,
                                                             _date=time.strftime(CST__DTIME_FORMAT),
                                                             _database_index=len(TARGET_DB) + \
                                                                             len(SELECT)),
                                       targettags= \
                                          create_target_tags(_parameters=CFG_PARAMETERS,
                                                             _hashid=hashid,
                                                             _filename_no_extens=fname_no_extens,
                                                             _path=dirpath,
                                                             _extension=extension,
                                                             _size=size,
                                                             _date=time.strftime(CST__DTIME_FORMAT),
                                                             _database_index=len(TARGET_DB) + \
                                                                             len(SELECT)))

                        msg("    + {0} selected \"{1}\" (file selected #{2})".format(prefix,
                                                                                     fullname,
                                                                                     len(SELECT)))
                        msg("       size={0}; date={1}".format(size,
                                                               time.strftime(CST__DTIME_FORMAT)))

                        SELECT_SIZE_IN_BYTES += size

                    else:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # tobeadded is False : let's discard <filename> :
                        number_of_discarded_files += 1

                        if ARGS.verbosity == 'high':
                            msg("    - {0} (similar hashid in the database) " \
                                " discarded \"{1}\"".format(prefix, fullname))

            else:
                msg("    ! browsing {0}, an error occured : " \
                    "can't read the file ".format(source_path),
                    _consolecolor='red')
                msg("    \"{0}\"".format(fullname),
                    _consolecolor='red')

    return fill_select__checks(_number_of_discarded_files=number_of_discarded_files,
                               _prefix=prefix,
                               _fullname=fullname)

#///////////////////////////////////////////////////////////////////////////////
def fill_select__checks(_number_of_discarded_files, _prefix, _fullname):
    """
        fill_select__checks()
        ________________________________________________________________________

        To be called at the end of fill_select() : remove some files from SELECT
        if they don't pass the checks :
                (1) future filename's can't be in conflict with another file in SELECT
                (2) future filename's can't be in conflict with another file already
                    stored in the target path.
        ________________________________________________________________________

        PARAMETERS :
                o _number_of_discarded_files    : (int) see fill_select()
                o _prefix                       : (str) see fill_select()
                o _fullname                     : (str) see fill_select()

        RETURNED VALUE
                (int) the number of discarded files
    """
    msg("    o checking that there's no anomaly with the selected files...")

    # (1) future filename's can't be in conflict with another file in SELECT
    msg("       ... let's check that future filenames aren't in conflict " \
        "with another file in SELECT...")
    to_be_discarded = []        # a list of hash.
    for (selectedfile_hash1, selectedfile_hash2) in itertools.combinations(SELECT, 2):

        if SELECT[selectedfile_hash1].targetname == SELECT[selectedfile_hash2].targetname:
            msg("    ! {0} discarded \"{1}\" : target filename \"{2}\" would be used " \
                "two times for two different files !".format(_prefix,
                                                             _fullname,
                                                             SELECT[selectedfile_hash2].targetname),
                _consolecolor="red")

            to_be_discarded.append(selectedfile_hash2)

    # (2) future filename's can't be in conflict with another file already
    # stored in the target path :
    if not CFG_PARAMETERS["target"]["mode"] == 'nocopy':
        msg("       ... let's check that future filenames aren't in conflict " \
            "with another file already")
        msg("           stored in the target path...")
        for selectedfile_hash in SELECT:
            if os.path.exists(os.path.join(normpath(ARGS.targetpath),
                                           SELECT[selectedfile_hash].targetname)):
                msg("    ! {0} discarded \"{1}\" : target filename \"{2}\" already " \
                    "exists in the target path !".format(_prefix,
                                                         _fullname,
                                                         SELECT[selectedfile_hash].targetname),
                    _consolecolor="red")

                to_be_discarded.append(selectedfile_hash)

    # final message and deletion :
    if len(to_be_discarded) == 0:
        msg("    o  everything ok : no anomaly detected. See details above.")
    else:
        if len(to_be_discarded) == 1:
            ending = "y"
        else:
            ending = "ies"
        msg("    !  beware : {0} anomal{1} detected. " \
            "See details above.".format(len(to_be_discarded),
                                        ending),
            _consolecolor="red")

        for _hash in to_be_discarded:
            # e.g. , _hash may have discarded two times (same target name + file
            # already present on disk), hence the following condition :
            if _hash in SELECT:
                del SELECT[_hash]
                _number_of_discarded_files += 1

    return _number_of_discarded_files

#///////////////////////////////////////////////////////////////////////////////
def get_database_fullname():
    """
        get_database_fullname()
        ________________________________________________________________________

          Return the full name (=full path + name) of the database in
        ARGS.targetpath .
        ________________________________________________________________________

        NO PARAMETER

        RETURNED VALUE
                the expected string
    """
    return os.path.join(normpath(ARGS.targetpath), CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)

#///////////////////////////////////////////////////////////////////////////////
def get_disk_free_space(_path):
    """
        get_disk_free_space()
        ________________________________________________________________________

        return the available space on disk() in bytes. Code for Windows system
        from http://stackoverflow.com/questions/51658/ .
        ________________________________________________________________________

        PARAMETER
                o _path : (str) the source path belonging to the disk to be
                          analysed.

        RETURNED VALUE
                the expected int(eger)
    """
    if CST__PLATFORM == 'Windows':
        free_bytes = ctypes.c_ulonglong(0)
        ctypes.windll.kernel32.GetDiskFreeSpaceExW(ctypes.c_wchar_p(_path),
                                                   None, None, ctypes.pointer(free_bytes))
        return free_bytes.value
    else:
        stat = os.statvfs(normpath(_path))
        return stat.f_bavail * stat.f_frsize

#///////////////////////////////////////////////////////////////////////////////
def get_filename_and_extension(_path):
    """
        get_filename_and_extension()
        ________________________________________________________________________

        Return
        ________________________________________________________________________

        PARAMETERS
                o  _path        : (str) the source path

        RETURNED VALUE
                (str)filename without extension, (str)the extension without the
                initial dot.
    """
    fname_no_extens, extension = os.path.splitext(_path)

    # the extension can't begin with a dot.
    if extension.startswith("."):
        extension = extension[1:]

    return fname_no_extens, extension

#///////////////////////////////////////////////////////////////////////////////
def get_logfile_fullname():
    """
        get_logfile_fullname()
        ________________________________________________________________________

        Return the logfile fullname
        ________________________________________________________________________

        no PARAMETER.

        RETURNED VALUE : the expected string
    """
    return os.path.join(CST__KATALSYS_SUBDIR,
                        CST__LOG_SUBSUBDIR,
                        CFG_PARAMETERS["log file"]["name"])

#///////////////////////////////////////////////////////////////////////////////
def goodbye(_timestamp_start):
    """
        goodbye()
        ________________________________________________________________________

        display a goodbye message.
        ________________________________________________________________________

        PARAMETER :
                o  _timestamp_start : a datetime.datetime object

        no RETURNED VALUE
    """
    msg("=== exit (Katal stopped at {0}; " \
        "total duration time : {1}) ===".format(datetime.now().strftime(CST__DTIME_FORMAT),
                                                datetime.now() - _timestamp_start))

#///////////////////////////////////////////////////////////////////////////////
def hashfile64(_filename, _stop_after=None):
    """
        hashfile64()
        ________________________________________________________________________

        return the footprint of a file, encoded with the base 64. If _stop_after
        is set to an integer, only the beginning of the file will be used to
        compute the hash (see CST__PARTIALHASHID_BYTESNBR constant).
        ________________________________________________________________________

        PARAMETER
                o _filename : (str) file's name
                o _stop_after:(None/int) if None, the file will be entirely read,
                              otherwise, only the first _stop_after bytes will
                              be read.
        RETURNED VALUE
                the expected string. If you use sha256 as a hasher, the
                resulting string will be 44 bytes long. E.g. :
                        "YLkkC5KqwYvb3F54kU7eEeX1i1Tj8TY1JNvqXy1A91A"
    """
    # hasher used by the hashfile64() function.
    hasher = hashlib.sha256()

    nbr_of_bytes_read = 0
    with open(_filename, "rb") as afile:
        # a buffer of 65536 bytes is an optimized buffer.
        buf = afile.read(65536)
        while len(buf) > 0:
            nbr_of_bytes_read += 65536
            if _stop_after is not None and nbr_of_bytes_read >= _stop_after:
                break

            hasher.update(buf)
            buf = afile.read(65536)

    return b64encode(hasher.digest()).decode()

#///////////////////////////////////////////////////////////////////////////////
def is_ntfs_prefix_mandatory(_path):
    """
        is_ntfs_prefix_mandatory()
        ________________________________________________________________________

        Return True if the _path is a path in a systemfile requiring the NTFS
        prefix for long filenames.
        ________________________________________________________________________

        PARAMETER
            _path : (str)the path to be tested

        RETURNED VALUE
            a boolean
    """
    longpath1 = os.path.join(_path, "a"*250)
    longpath1 = os.path.normpath(os.path.abspath(os.path.expanduser(longpath1)))

    longpath2 = os.path.join(longpath1, "b"*250)

    res = False
    try:
        os.makedirs(longpath2)
    except IOError:
        res = True

    try:
        shutil.rmtree(longpath1)
    except IOError:
        pass

    return res

#///////////////////////////////////////////////////////////////////////////////
def logfile_opening():
    """
        logfile_opening()
        ________________________________________________________________________

          Open the log file in "a" mode, initialize LOGFILE_SIZE and return
        the result of the call to open().
          If the ancient logfile exists, it is renamed to avoid its overwriting.
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                the _io.BufferedReader object returned by the call to open()
    """
    global LOGFILE_SIZE
    logfile_fullname = get_logfile_fullname()

    if os.path.exists(normpath(logfile_fullname)):
        LOGFILE_SIZE = os.stat(normpath(logfile_fullname)).st_size
    else:
        LOGFILE_SIZE = 0

    return open(logfile_fullname, "a")

#///////////////////////////////////////////////////////////////////////////////
def main():
    """
        main()
        ________________________________________________________________________

        Main entry point.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE

        This function should NOT have arguments : otherwise, the entrypoint
        defined in setup.py would not be valid.

        o  sys.exit(-1) is called if the config file is ill-formed.
        o  sys.exit(-2) is called if a KatalError exception is raised
        o  sys.exit(-3) is called if another exception is raised
    """
    global ARGS

    timestamp_start = datetime.now()

    try:
        ARGS = read_command_line_arguments()
        check_args()

        welcome(timestamp_start)
        main_warmup(timestamp_start)
        main_actions_tags()
        main_actions()

        goodbye(timestamp_start)

        if USE_LOGFILE:
            LOGFILE.close()

    except KatalError as exception:
        print("({0}) ! a critical error occured.\nError message : {1}".format(__projectname__,
                                                                              exception))
        sys.exit(-2)
    else:
        sys.exit(-3)

    sys.exit(0)

#///////////////////////////////////////////////////////////////////////////////
def main_actions():
    """
        main_actions()
        ________________________________________________________________________

        Call the different actions required by the arguments of the command line.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    if ARGS.cleandbrm:
        action__cleandbrm()

    if ARGS.reset:
        action__reset()

    if ARGS.targetkill:
        action__target_kill(ARGS.targetkill)

    if ARGS.whatabout:
        read_target_db()
        action__whatabout(ARGS.whatabout)

    if ARGS.select:
        read_target_db()
        read_filters()
        action__select()

        if ARGS.verbosity != 'none' and len(SELECT) > 0:
            answer = \
                input("\nDo you want to update the target database and to {0} the selected " \
                      "files into the target directory " \
                      "(\"{1}\") ? (y/N) ".format(CFG_PARAMETERS["target"]["mode"],
                                                  ARGS.targetpath))

            if answer in ("y", "yes"):
                action__add()
                show_infos_about_target_path()

    if ARGS.add:
        read_target_db()
        read_filters()
        action__select()
        action__add()
        show_infos_about_target_path()

    if ARGS.new:
        action__new(ARGS.new)

    if ARGS.rebase:
        action__rebase(ARGS.rebase)

    if ARGS.findtag:
        action__findtag(ARGS.findtag)

    if ARGS.downloaddefaultcfg is not None:
        action__downloadefaultcfg(_targetname=CST__DEFAULT_CONFIGFILE_NAME,
                                  _location=ARGS.downloaddefaultcfg)

#///////////////////////////////////////////////////////////////////////////////
def main_actions_tags():
    """
        main_actions_tags()
        ________________________________________________________________________

        Call the different actions required by the arguments of the command line.
        Function dedicated to the operations on tags.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    if ARGS.rmnotags:
        action__rmnotags()

    if ARGS.settagsstr:
        action__settagsstr(ARGS.settagsstr, ARGS.to)

    if ARGS.addtag:
        action__addtag(ARGS.addtag, ARGS.to)

    if ARGS.rmtags:
        action__rmtags(ARGS.to)

#///////////////////////////////////////////////////////////////////////////////
def main_warmup(_timestamp_start):
    """
        main_warmup()
        ________________________________________________________________________

        Initializations :

            if the --new/--downloaddefaultcfg options have not be used :

            o configfile_name = None / a string
            o reading of the configuration file
            o list of the expected directories : if one directory is missing, let's create it.
              create_subdirs_in_target_path()
            o welcome_in_logfile()
            o warning if source path == target path
            o --infos
            o -si / --sourceinfos
            o -ti / --targetinfos
        ________________________________________________________________________

        PARAMETER :
                o  _timestamp_start : a datetime.datetime object

        no RETURNED VALUE

        o  sys.exit(-1) is called if the expected config file is ill-formed or missing.
    """
    global CFG_PARAMETERS, LOGFILE

    #...........................................................................
    # a special case : if the options --new//--downloaddefaultcfg have been used, let's quit :
    if ARGS.new is not None or ARGS.downloaddefaultcfg is not None:
        return

    #...........................................................................
    # let's find a config file to be read :
    configfile_name, configfile_name__err = where_is_the_configfile()

    if configfile_name__err < 0:
        # ill-formed config file :
        sys.exit(-1)

    if configfile_name__err > 0:
        # see the code's error of the where_is_the_configfile() function.
        return

    #...........................................................................
    # let's read the config file :
    CFG_PARAMETERS = read_parameters_from_cfgfile(configfile_name)
    if CFG_PARAMETERS is None:
        # ill-formed config file :
        sys.exit(-1)
    else:
        msg("    ... config file found and read (ok)")

    if CFG_PARAMETERS["target"]["mode"] == 'move':
        msg("  = mode=move                                                             =",
            _consolecolor="cyan")
        msg("  =     the files will be moved (NOT copied) in the target directory      =",
            _consolecolor="cyan")

    if CFG_PARAMETERS["target"]["mode"] == 'nocopy':
        msg("  = mode=nocopy                                                           =",
            _consolecolor="cyan")
        msg("  =     the files will NOT be copied or moved in the target directory     =",
            _consolecolor="cyan")

    source_path = CFG_PARAMETERS["source"]["path"]

    #...........................................................................
    # list of the expected directories : if one directory is missing, let's create it.
    create_subdirs_in_target_path()

    #...........................................................................
    if USE_LOGFILE:
        LOGFILE = logfile_opening()
        welcome_in_logfile(_timestamp_start)

    #...........................................................................
    if ARGS.targetpath == source_path:
        msg("  ! warning : " \
            "source path and target path have the same value, " \
            "namely \"{0}\" (path: \"{1}\")".format(ARGS.targetpath, normpath(ARGS.targetpath)),
            _consolecolor="red")

    #...........................................................................
    # we show the following informations :
    for path, info in ((configfile_name, "config file"),
                       (os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR), "trash subdir"),
                       (os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TASKS_SUBSUBDIR), "tasks subdir"),
                       (os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR), "log subdir"),):
        msg("  = let's use \"{0}\" as {1}".format(path, info))

    msg("  = source directory : \"{0}\" (path : \"{1}\")".format(source_path,
                                                                 normpath(source_path)))

    #...........................................................................
    if ARGS.infos:
        action__infos()

    #...........................................................................
    if ARGS.sourceinfos:
        show_infos_about_source_path()

    #...........................................................................
    if ARGS.targetinfos:
        show_infos_about_target_path()

#///////////////////////////////////////////////////////////////////////////////
def modify_the_tag_of_some_files(_tag, _to, _mode):
    """
        modify_the_tag_of_some_files()
        ________________________________________________________________________

        Modify the tag(s) of some files.
        ________________________________________________________________________

        PARAMETERS
                o _tag          : (str) new tag(s)
                o _to           : (str) a string (wildcards accepted) describing
                                   what files are concerned
                o _mode         : (str) "append" to add _tag to the other tags
                                        "set" to replace old tag(s) by a new one
    """
    if not os.path.exists(normpath(get_database_fullname())):
        msg("    ! no database found.",
            _consolecolor="red")
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        files_to_be_modified = []       # a list of (hashids, name)
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if fnmatch.fnmatch(db_record["name"], _to):
                files_to_be_modified.append((db_record["hashid"], db_record["name"]))

        if len(files_to_be_modified) == 0:
            msg("    * no files match the given name(s) given as a parameter.")
        else:
            # let's apply the tag(s) to the <files_to_be_modified> :
            for hashid, filename in files_to_be_modified:

                msg("    o applying the tag string \"{0}\" to {1}.".format(_tag, filename))

                if ARGS.off:
                    pass

                elif _mode == "set":
                    sqlorder = 'UPDATE dbfiles SET tagsstr=? WHERE hashid=?'
                    db_connection.execute(sqlorder, (_tag, hashid))

                elif _mode == "append":
                    sqlorder = 'UPDATE dbfiles SET tagsstr = tagsstr || \"{0}{1}\" ' \
                               'WHERE hashid=\"{2}\"'.format(CST__TAG_SEPARATOR, _tag, hashid)
                    db_connection.executescript(sqlorder)

                else:
                    raise KatalError("_mode argument \"{0}\" isn't known".format(_mode))

            db_connection.commit()

        db_connection.close()

#///////////////////////////////////////////////////////////////////////////////
def msg(_msg, _for_console=True, _for_logfile=True, _consolecolor=None):
    """
        msg()
        ________________________________________________________________________

        Display a message on console, write the same message in the log file.
        The message isn't displayed on console if ARGS.verbosity has been set to
        'none' (see the --verbosity argument) .
        ________________________________________________________________________

        PARAMETERS
                o _msg          : (str) the message to be written
                o _for_console  : (bool) authorization to write on console
                o _for_logfile  : (bool) authorization to write in the log file
                o _consolecolor : (None/str) see CST__LINUXCONSOLECOLORS
                                  The color will be displayed on console, not
                                  in the log file.

        no RETURNED VALUE
    """
    global LOGFILE, LOGFILE_SIZE

    final_msg = _msg + "\n"

    # first to the console : otherwise, if an error occurs by writing to the log
    # file, it would'nt possible to read the message.
    if ARGS.verbosity != 'none' and _for_console:
        if _consolecolor is None or CST__PLATFORM == 'Windows':
            sys.stdout.write(_msg+"\n")
        else:
            sys.stdout.write(CST__LINUXCONSOLECOLORS[_consolecolor])
            sys.stdout.write(_msg+"\n")
            sys.stdout.write(CST__LINUXCONSOLECOLORS["default"])

    # secondly, to the logfile :
    if USE_LOGFILE and _for_logfile and LOGFILE is not None:
        if LOGFILE_SIZE + len(final_msg) > int(CFG_PARAMETERS["log file"]["maximal size"]):
            # let's force writing on disk...
            LOGFILE.flush()
            os.fsync(LOGFILE)
            # ... before closing :
            LOGFILE.close()
            # let's backup the current log file :
            backup_logfile(get_logfile_fullname())
            # let's remove the current log file's content :
            os.remove(get_logfile_fullname())
            # let's open a new log file :
            LOGFILE = logfile_opening()

        LOGFILE.write(final_msg)
        LOGFILE_SIZE += len(final_msg)

#///////////////////////////////////////////////////////////////////////////////
def normpath(_path):
    """
        normpath()
        ________________________________________________________________________

        Return a human-readable (e.g. "~" -> "/home/myhome/" on Linux systems),
        normalized version of a path.

        The returned string may be used as a parameter given to by
        os.path.exists() .

        about the "\\\\?\\" prefix, see e.g. this thread on StackOverflow :
        http://stackjava-script.com/questions/1365797/
        the prefix allows Windows to deal with path whose length is greater than
        260 characters.
        ________________________________________________________________________

        PARAMETER : (str)_path

        RETURNED VALUE : the expected string
    """
    res = os.path.normpath(os.path.abspath(os.path.expanduser(_path)))

    if ARGS.usentfsprefix:
        res = res.replace("\\\\?\\", "")

    if res == ".":
        res = os.getcwd()

    if ARGS.usentfsprefix:
        res = "\\\\?\\"+res

    return res

#///////////////////////////////////////////////////////////////////////////////
def read_command_line_arguments():
    """
        read_command_line_arguments()
        ________________________________________________________________________

        Read the command line arguments.
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                return the argparse object.
    """
    parser = \
      argparse.ArgumentParser(description="{0} v. {1}".format(__projectname__, __version__),
                              epilog="{0} v. {1} ({2}), " \
                                     "a project by {3} " \
                                     "({4})".format(__projectname__,
                                                    __version__,
                                                    __license__,
                                                    __author__,
                                                    __email__),
                              formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('--add',
                        action="store_true",
                        help="# Select files according to what is described " \
                             "in the configuration file " \
                             "then add them to the target directory. " \
                             "This option can't be used with the --select one." \
                             "If you want more informations about the process, please " \
                             "use this option in combination with --infos .")

    parser.add_argument('--addtag',
                        type=str,
                        help="# Add a tag to some file(s) in combination " \
                             "with the --to option. ")

    parser.add_argument('-cfg', '--configfile',
                        type=str,
                        help="# Set the name of the config file, e.g. config.ini")

    parser.add_argument('--cleandbrm',
                        action="store_true",
                        help="# Remove from the database the missing files in the target path.")

    parser.add_argument('--copyto',
                        type=str,
                        help="# To be used with the --findtag parameter. Copy the found files " \
                              "into an export directory.")

    parser.add_argument('-dlcfg', '--downloaddefaultcfg',
                        choices=("local", "home",),
                        help="# Download the default config file and overwrite the file having " \
                             "the same name. This is done before the script reads the parameters " \
                             "in the config file. Use 'local' to download in the current " \
                             "directory, 'home' to download in the user's HOME directory.")

    parser.add_argument('--findtag',
                        type=str,
                        help="# Find the files in the target directory with the given tag. " \
                             "The tag is a simple string, not a regex.")

    parser.add_argument('--infos',
                        action="store_true",
                        help="# Display informations about the source directory " \
                             "given in the configuration file. Help the --select/--add " \
                             "options to display more informations about the process : in " \
			     "this case, the --infos will be executed before --select/--add")

    parser.add_argument('-n', '--new',
                        type=str,
                        help="# Create a new target directory")

    parser.add_argument('--off',
                        action="store_true",
                        help="# Don't write anything into the target directory or into " \
                             "the database, except into the current log file. " \
                             "Use this option to simulate an operation : you get the messages " \
                             "but no file is modified on disk, no directory is created.")

    parser.add_argument('--rebase',
                        type=str,
                        help="# Copy the current target directory into a new one : you " \
                             "rename the files in the target directory and in the database. " \
                             "First, use the --new option to create a new target directory, " \
                             "modify the .ini file of the new target directory " \
                             "(modify [target]name of the target files), " \
                             "then use --rebase with the name of the new target directory")

    parser.add_argument('--reset',
                        action="store_true",
                        help="# Delete the database and the files in the target directory")

    parser.add_argument('--rmnotags',
                        action="store_true",
                        help="# Remove all files without a tag")

    parser.add_argument('--rmtags',
                        action="store_true",
                        help="# Remove all the tags of some file(s) in combination " \
                             "with the --to option. ")

    parser.add_argument('-s', '--select',
                        action="store_true",
                        help="# Select files according to what is described " \
                             "in the configuration file " \
                             "without adding them to the target directory. " \
                             "This option can't be used with the --add one." \
                             "If you want more informations about the process, please " \
                             "use this option in combination with --infos .")

    parser.add_argument('--settagsstr',
                        type=str,
                        help="# Give the tag to some file(s) in combination " \
                             "with the --to option. " \
                             "Overwrite the ancient tag string. " \
                             "If you want to empty the tags' string, please use a space, " \
                             "not an empty string : otherwise the parameter given " \
                             "to the script wouldn't be taken in account by the shell")

    parser.add_argument('-si', '--sourceinfos',
                        action="store_true",
                        help="# Display informations about the source directory")

    parser.add_argument('--strictcmp',
                        action="store_true",
                        help="# To be used with --add or --select. Force a bit-to-bit comparision" \
                             "between files whose hashid-s is equal.")

    parser.add_argument('--targetpath',
                        type=str,
                        default=".",
                        help="# Target path, usually '.' . If you set path to . (=dot character)" \
                             ", it means that the source path is the current directory" \
                             " (=the directory where the script katal.py has been launched)")

    parser.add_argument('-ti', '--targetinfos',
                        action="store_true",
                        help="# Display informations about the target directory")

    parser.add_argument('-tk', '--targetkill',
                        type=str,
                        help="# Kill (=move to the trash directory) one file from " \
                             "the target directory." \
                             "DO NOT GIVE A PATH, just the file's name, " \
                             "without the path to the target directory")

    parser.add_argument('--to',
                        type=str,
                        help="# Give the name of the file(s) concerned by --settagsstr. " \
                        "wildcards accepted; e.g. to select all .py files, use '*.py' . " \
                        "Please DON'T ADD the path to the target directory, only the filenames")

    parser.add_argument('--usentfsprefix',
                        action="store_true",
                        help="# Force the script to prefix filenames by a special string " \
                             "required by the NTFS for long filenames, namely \\\\?\\")

    parser.add_argument('--verbosity',
                        choices=("none", "normal", "high"),
                        default='normal',
                        help="# Console verbosity : " \
                             "'none'=no output to the console, no question asked on the console; " \
                             "'normal'=messages to the console " \
                             "and questions asked on the console; " \
                             "'high'=display discarded files. A question may be asked only by " \
                             "using the following arguments : " \
                             "--new, --rebase, --reset and --select")

    parser.add_argument('--version',
                        action='version',
                        version="{0} v. {1}".format(__projectname__, __version__),
                        help="# Show the version and exit")

    parser.add_argument('--whatabout',
                        type=str,
                        help="# Say if the file[the files in a directory] already in the " \
                             "given as a parameter is in the target directory " \
                             "notwithstanding its name.")

    return parser.parse_args()

#///////////////////////////////////////////////////////////////////////////////
def possible_paths_to_cfg():
    """
        possible_paths_to_cfg()
        ________________________________________________________________________

        return a list of the (str)paths to the config file, without the name
        of the file.

          The first element of the list is the local directory + ".katal",
        the last element of the list is ~ + .katal .
        ________________________________________________________________________

        NO PARAMETER.

        RETURNED VALUE : the expected list of strings.
    """
    res = []

    res.append(os.path.os.path.join(normpath("."),
                                    normpath(ARGS.targetpath),
                                    CST__KATALSYS_SUBDIR))

    if CST__PLATFORM == 'Windows':
        res.append(os.path.join(os.path.expanduser("~"),
                                "Local Settings",
                                "Application Data",
                                "katal"))

    res.append(os.path.join(os.path.expanduser("~"),
                            ".katal"))

    return res

#///////////////////////////////////////////////////////////////////////////////
def read_parameters_from_cfgfile(_configfile_name):
    """
        read_parameters_from_cfgfile()
        ________________________________________________________________________

        Read the configfile and return the parser or None if an error occured.

        If the mode is set to 'nocopy', parser["target"]["name of the target files"]
        is set to "%i" .
        ________________________________________________________________________

        PARAMETER
                o _configfile_name       : (str) config file name (e.g. katal.ini)

        RETURNED VALUE
                None if an error occured while reading the configuration file
                or the expected configparser.ConfigParser object=.
    """
    global USE_LOGFILE

    parser = configparser.ConfigParser()

    try:
        parser.read(_configfile_name)
        USE_LOGFILE = parser["log file"]["use log file"] == "True"
        # just to check the existence of the following values in the configuration file :
        _ = parser["log file"]["maximal size"]
        _ = parser["log file"]["name"]
        _ = parser["target"]["name of the target files"]
        _ = parser["target"]["mode"]
        _ = parser["source"]["eval"]
        _ = parser["display"]["target filename.max length on console"]
        _ = parser["display"]["hashid.max length on console"]
        _ = parser["display"]["tag.max length on console"]
        _ = parser["display"]["source filename.max length on console"]
        _ = parser["source"]["path"]
    except KeyError as exception:
        msg("  ! An error occured while reading " \
            "the config file \"{0}\".".format(_configfile_name),
            _consolecolor="red")
        msg("  ! Your configuration file lacks a specific value : \"{0}\".".format(exception),
            _consolecolor="red")
        msg("  ... you should download a new default config file : " \
            "see -dlcfg/--downloaddefaultcfg option",
            _consolecolor="red")
        return None
    except BaseException as exception:
        msg("  ! An error occured while reading " \
            "the config file \"{0}\".".format(_configfile_name),
            _consolecolor="red")
        msg("  ! Python message : \"{0}\"".format(exception),
            _consolecolor="red")
        return None

    if parser["target"]["mode"] == 'nocopy':
        #   configparser.ConfigParser objects have to be initialized with strings
        # exactly equal to the strings read in an .ini file : so instead of the
        # natural "%i" we have to write "%%i" :
        parser["target"]["name of the target files"] = "%%i"

        msg("  *  since 'mode'=='nocopy', the value of \"[target]name of the target files\" ",
            _consolecolor="cyan")
        msg("     is neutralized and set to '%i' (i.e. the database index : '1', '2', ...)",
            _consolecolor="cyan")

    return parser

#///////////////////////////////////////////////////////////////////////////////
def read_filters():
    """
        read_filters()
        ________________________________________________________________________

        Initialize FILTERS from the configuration file.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    FILTERS.clear()

    stop = False
    filter_index = 1

    while not stop:
        if not CFG_PARAMETERS.has_section("source.filter"+str(filter_index)):
            stop = True
        else:
            FILTERS[filter_index] = dict()

            if CFG_PARAMETERS.has_option("source.filter"+str(filter_index), "name"):
                FILTERS[filter_index]["name"] = \
                             re.compile(CFG_PARAMETERS["source.filter"+str(filter_index)]["name"])

            if CFG_PARAMETERS.has_option("source.filter"+str(filter_index), "iname"):
                FILTERS[filter_index]["name"] = \
                             re.compile(CFG_PARAMETERS["source.filter"+str(filter_index)]["iname"],
                                        re.IGNORECASE)

            if CFG_PARAMETERS.has_option("source.filter"+str(filter_index), "size"):
                FILTERS[filter_index]["size"] = \
                              CFG_PARAMETERS["source.filter"+str(filter_index)]["size"]

            if CFG_PARAMETERS.has_option("source.filter"+str(filter_index), "date"):
                FILTERS[filter_index]["date"] = \
                              CFG_PARAMETERS["source.filter"+str(filter_index)]["date"]

        filter_index += 1

#///////////////////////////////////////////////////////////////////////////////
def read_target_db():
    """
        read_target_db()
        ________________________________________________________________________

        Read the database stored in the target directory and initialize
        TARGET_DB.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    if not os.path.exists(normpath(get_database_fullname())):
        create_empty_db(normpath(get_database_fullname()))

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        TARGET_DB[db_record["hashid"]] = (db_record["partialhashid"],
                                          db_record["size"],
                                          db_record["sourcename"])

    db_connection.close()

#/////////////////////////////////////////////////////////////////////////////////////////
def remove_illegal_characters(_src):
    """
        remove_illegal_characters()
        ________________________________________________________________________

        Replace some illegal characters by the underscore character. Use this function
        to create files on various plateforms.
        ________________________________________________________________________

        PARAMETER
                o _src   : (str) the source string

        RETURNED VALUE
                the expected string, i.e. <_src> without illegal characters.
    """
    res = _src
    for char in ("*", "/", "\\", ".", "[", "]", ":", ";", "|", "=", ",", "?", "<", ">", "-", " "):
        res = res.replace(char, "_")
    return res

#///////////////////////////////////////////////////////////////////////////////
def shortstr(_str, _max_length):
    """
        shortstr()
        ________________________________________________________________________

        The function returns a shortened version of a string.
        ________________________________________________________________________

        PARAMETER
                o _str          : (src) the source string
                o _max_length   : (int) the maximal length of the string

        RETURNED VALUE
                the expected string
    """
    if len(_str) > _max_length:
        return "[...]"+_str[-(_max_length-5):]
    return _str

#///////////////////////////////////////////////////////////////////////////////
def show_infos_about_source_path():
    """
        show_infos_about_source_path()
        ________________________________________________________________________

        Display informations about the source directory.
		Initialize INFOS_ABOUT_SRC_PATH.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    global INFOS_ABOUT_SRC_PATH

    source_path = CFG_PARAMETERS["source"]["path"]

    msg("  = informations about the \"{0}\" " \
        "(path: \"{1}\") source directory =".format(source_path,
                                                    normpath(source_path)))

    if not os.path.exists(normpath(source_path)):
        msg("    ! can't find source path \"{0}\" .".format(source_path),
            _consolecolor="red")
        return
    if not os.path.isdir(normpath(source_path)):
        msg("    ! source path \"{0}\" isn't a directory .".format(source_path),
            _consolecolor="red")
        return

    if is_ntfs_prefix_mandatory(source_path):
        msg("    ! the source path should be used with the NTFS prefix for long filenames.",
            _consolecolor="red")

        if not ARGS.usentfsprefix:
            msg("    ! ... but the --usentfsprefix argument wasn't given !",
                _consolecolor="red")
            msg("    ! You may encounter an IOError, or a FileNotFound error.",
                _consolecolor="red")
            msg("    ! If so, please use the --usentfsprefix argument.",
                _consolecolor="red")
            msg("")

    total_size = 0
    files_number = 0
    files_number_interval = 0   # used to display the intermediate number, see below.
    extensions = dict()  # (str)extension : [number of files, total size]
    for dirpath, _, fnames in os.walk(normpath(source_path)):
        for filename in fnames:
            fullname = os.path.join(normpath(dirpath), filename)

            # ..................................................................
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link on the
            #   "size = os.stat(normpath(fullname)).st_size" line (see below).
            # ..................................................................
            if os.path.exists(fullname):
                size = os.stat(normpath(fullname)).st_size
                extension = os.path.splitext(normpath(filename))[1]

                if extension in extensions:
                    extensions[extension][0] += 1
                    extensions[extension][1] += size
                else:
                    extensions[extension] = [1, size]

                total_size += size
                files_number += 1

                files_number_interval += 1
                if files_number_interval == 100000:
                    msg("    ... already {0} files read in the source directory, " \
                        "still processing...".format(files_number_interval))
                    files_number_interval = 0
            else:
                msg("    ! browsing {0}, an error occured : " \
                    "can't read the file ".format(source_path),
                    _consolecolor='red')
                msg("    \"{0}\"".format(fullname),
                    _consolecolor='red')

    msg("    o files number : {0} file(s)".format(files_number))
    msg("    o total size : {0}".format(size_as_str(total_size)))
    msg("    o list of all extensions ({0} extension(s) found): ".format(len(extensions)))
    for extension in sorted(extensions, key=lambda s: s.lower()):
        msg("      - {0:15} : {1} files, {2}".format(extension,
                                                     extensions[extension][0],
                                                     size_as_str(extensions[extension][1])))

    INFOS_ABOUT_SRC_PATH = (total_size, files_number, extensions)

#///////////////////////////////////////////////////////////////////////////////
def show_infos_about_target_path():
    """
        show_infos_about_target_path()
        ________________________________________________________________________

        Display informations about the the target directory
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                (int) 0 if ok, -1 if an error occured
    """
    #...........................................................................
    msg("  = informations about the \"{0}\" " \
        "(path: \"{1}\") target directory =".format(ARGS.targetpath,
                                                    normpath(ARGS.targetpath)))

    #...........................................................................
    if is_ntfs_prefix_mandatory(ARGS.targetpath):
        msg("    ! the target path should be used with the NTFS prefix for long filenames.",
            _consolecolor="red")

        if not ARGS.usentfsprefix:
            msg("    ! ... but the --usentfsprefix argument wasn't given !",
                _consolecolor="red")
            msg("    ! You may encounter an IOError, or a FileNotFound error.",
                _consolecolor="red")
            msg("    ! If so, please use the --usentfsprefix argument.",
                _consolecolor="red")
            msg("")

    #...........................................................................
    if not os.path.exists(normpath(ARGS.targetpath)):
        msg("Can't find target path \"{0}\".".format(ARGS.targetpath))
        return -1

    if not os.path.isdir(normpath(ARGS.targetpath)):
        msg("target path \"{0}\" isn't a directory.".format(ARGS.targetpath))
        return -1

    if not os.path.exists(os.path.join(normpath(ARGS.targetpath),
                                       CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)):
        msg("    o no database in the target directory.")
        return 0

    #...........................................................................
    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    # there's no easy way to know the size of a table in a database,
    # so we can't display the "empty database" warning before the following
    # code which reads the table.
    rows_data = []
    row_index = 0
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        sourcedate = \
            datetime.utcfromtimestamp(db_record["sourcedate"]).strftime(CST__DTIME_FORMAT)

        if CFG_PARAMETERS["target"]["mode"] != 'nocopy':
            rows_data.append((db_record["hashid"],
                              db_record["name"],
                              tagsstr_repr(db_record["tagsstr"]),
                              db_record["sourcename"],
                              sourcedate))
        else:
            rows_data.append((db_record["hashid"],
                              tagsstr_repr(db_record["tagsstr"]),
                              db_record["sourcename"],
                              sourcedate))
        row_index += 1

    if row_index == 0:
        msg("    ! (empty database)",
            _consolecolor="red")
        return 0

    msg("    o {0} file(s) in the database :".format(row_index))

    targetname_maxlength = \
            int(CFG_PARAMETERS["display"]["target filename.max length on console"])
    hashid_maxlength = \
            int(CFG_PARAMETERS["display"]["hashid.max length on console"])
    tagsstr_maxlength = \
            int(CFG_PARAMETERS["display"]["tag.max length on console"])
    sourcename_maxlength = \
            int(CFG_PARAMETERS["display"]["source filename.max length on console"])

    # beware : characters like "║" are forbidden (think to the cp1252 encoding
    # required by Windows terminal)
    if CFG_PARAMETERS["target"]["mode"] != 'nocopy':
        draw_table(_rows=(("hashid/base64", hashid_maxlength, "|"),
                          ("name", targetname_maxlength, "|"),
                          ("tags", tagsstr_maxlength, "|"),
                          ("source name", sourcename_maxlength, "|"),
                          ("source date", CST__DTIME_FORMAT_LENGTH, "|")),
                   _data=rows_data)
    else:
        draw_table(_rows=(("hashid/base64", hashid_maxlength, "|"),
                          ("tags", tagsstr_maxlength, "|"),
                          ("source name", sourcename_maxlength, "|"),
                          ("source date", CST__DTIME_FORMAT_LENGTH, "|")),
                   _data=rows_data)

    db_connection.close()

    return 0

#///////////////////////////////////////////////////////////////////////////////
def size_as_str(_size):
    """
        size_as_str()
        ________________________________________________________________________

        Return a size in bytes as a human-readable string.
        ________________________________________________________________________

        PARAMETER
                o _size         : (int) size in bytes

        RETURNED VALUE
                a str(ing)
    """
    if _size == 0:
        res = "0 byte"
    elif _size < 1e3:
        res = "{0} bytes".format(_size)
    elif _size < 9e3:
        res = "{0} kB ({1} bytes)".format(_size/1e3, _size)
    elif _size < 9e6:
        res = "~{0:.2f} MB ({1} bytes)".format(_size/1e6, _size)
    elif _size < 9e9:
        res = "~{0:.2f} GB ({1} bytes)".format(_size/1e9, _size)
    elif _size < 9e12:
        res = "~{0:.2f} TB ({1} bytes)".format(_size/1e12, _size)
    elif _size < 9e15:
        res = "~{0:.2f} PB ({1} bytes)".format(_size/1e15, _size)
    elif _size < 9e18:
        res = "~{0:.2f} EB ({1} bytes)".format(_size/1e18, _size)
    else:
        res = "~{0:.2f} ZB ({1} bytes)".format(_size/1e21, _size)

    return res

#//////////////////////////////////////////////////////////////////////////////
def tagsstr_repr(_tagsstr):
    """
        tagsstr_repr()
        ________________________________________________________________________

        Improve the way a tags' string can be displayed.
        ________________________________________________________________________

        PARAMETER
            _tagsstr : the raw tags' string

        RETURNED VALUE
            the expected (str)string
    """
    # let's remove the first tag separator :
    tagsstr = _tagsstr
    if tagsstr.startswith(CST__TAG_SEPARATOR):
        tagsstr = tagsstr[1:]

    return tagsstr

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__db(_filename, _size):
    """
        thefilehastobeadded__db()
        ________________________________________________________________________

        Return True if the file isn't already known in the database.
        ________________________________________________________________________

        PARAMETERS
                o _filename     : (str) file's name
                o _size         : (int) file's size, in bytes.

        RETURNED VALUE
                either (False, None, None)
                either (True, partial hashid, hashid)
    """
    # a list of hashid(s) :
    res = []

    # (1) how many file(s) in the database have a size equal to _size ?
    for hashid in TARGET_DB:
        _, target_size, _ = TARGET_DB[hashid]
        if target_size == _size:
            res.append(hashid)

    if len(res) == 0:
        return (True,
                hashfile64(_filename=_filename,
                           _stop_after=CST__PARTIALHASHID_BYTESNBR),
                hashfile64(_filename=_filename))

    # (2) how many file(s) among those in <res> have a partial hashid equal
    # to the partial hashid of _filename ?
    new_res = []
    src_partialhashid = hashfile64(_filename=_filename,
                                   _stop_after=CST__PARTIALHASHID_BYTESNBR)
    for hashid in res:
        target_partialhashid, _, _ = TARGET_DB[hashid]
        if target_partialhashid == src_partialhashid:
            new_res.append(hashid)

    res = new_res
    if len(res) == 0:
        return (True,
                src_partialhashid,
                hashfile64(_filename=_filename))

    # (3) how many file(s) among those in <res> have an hashid equal to the
    # hashid of _filename ?
    new_res = []
    src_hashid = hashfile64(_filename=_filename)
    for hashid in res:
        target_hashid, _, _ = TARGET_DB[hashid]
        if target_hashid == src_hashid:
            new_res.append(hashid)

    res = new_res
    if len(res) == 0:
        return (True,
                src_partialhashid,
                src_hashid)

    if not ARGS.strictcmp:
        return (False, None, None)

    # (4) bit-to-bit comparision :
    for hashid in res:
        if not filecmp.cmp(_filename, TARGET_DB[hashid][2], shallow=False):
            return (True,
                    src_partialhashid,
                    src_hashid)

    return (False, None, None)

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__filters(_filename, _size, _date):
    """
        thefilehastobeadded__filters()
        ________________________________________________________________________

        Return True if a file (_filename, _size) can be choosed and added to
        the target directory, according to the filters (stored in FILTERS).
        ________________________________________________________________________

        PARAMETERS
                o _filename     : (str) file's name
                o _size         : (int) file's size, in bytes.
                o _date         : (str) file's date

        RETURNED VALUE
                a boolean, giving the expected answer
    """
    evalstr = CFG_PARAMETERS["source"]["eval"]

    for filter_index in FILTERS:
        _filter = FILTERS[filter_index]

        evalstr = evalstr.replace("filter"+str(filter_index),
                                  str(eval_filter_for_a_file(_filter, _filename, _size, _date)))

    try:
        # eval() IS a dangerous function : see the note about CST__AUTHORIZED_EVALCHARS.
        for char in evalstr:
            if char not in CST__AUTHORIZED_EVALCHARS:
                raise KatalError("Error in configuration file : " \
                                   "trying to compute the \"{0}\" string; " \
                                   "wrong character '{1}'({2}) " \
                                   "used in the string to be evaluated. " \
                                   "Authorized " \
                                   "characters are " \
                                   "{3}".format(evalstr,
                                                char,
                                                unicodedata.name(char),
                                                "|"+"|".join(CST__AUTHORIZED_EVALCHARS)))
        return eval(evalstr)

    except BaseException as exception:
        raise KatalError("The eval formula in the config file (\"{0}\")" \
                           "contains an error. Python message : \"{1}\"".format(evalstr,
                                                                                exception))

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__filt_date(_filter, _date):
    """
        thefilehastobeadded__filt_date()
        ________________________________________________________________________

        Function used by thefilehastobeadded__filters() : check if the date of a
        file matches the filter given as a parameter.
        ________________________________________________________________________

        PARAMETERS
                o _filter        : a dict object; see documentation:selection
                o _date         : (str) file's datestamp (object datetime.datetime)

        RETURNED VALUE
                the expected boolean
    """
    # beware ! the order matters (<= before <, >= before >)
    if _filter["date"].startswith("="):
        return _date == datetime.strptime(_filter["date"][1:], CST__DTIME_FORMAT)
    elif _filter["date"].startswith(">="):
        return _date >= datetime.strptime(_filter["date"][2:], CST__DTIME_FORMAT)
    elif _filter["date"].startswith(">"):
        return _date > datetime.strptime(_filter["date"][1:], CST__DTIME_FORMAT)
    elif _filter["date"].startswith("<="):
        return _date < datetime.strptime(_filter["date"][2:], CST__DTIME_FORMAT)
    elif _filter["date"].startswith("<"):
        return _date < datetime.strptime(_filter["date"][1:], CST__DTIME_FORMAT)
    else:
        raise KatalError("Can't analyse a 'date' field : "+_filter["date"])

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__filt_name(_filter, _filename):
    """
        thefilehastobeadded__filt_name()
        ________________________________________________________________________

        Function used by thefilehastobeadded__filters() : check if the name of a
        file matches the filter given as a parameter.
        ________________________________________________________________________

        PARAMETERS
                o _filter           : a dict object; see documentation:selection
                o _filename         : (str) file's name

        RETURNED VALUE
                the expected boolean
    """
    # nb : _filter["name"] can either be a case sensitive regex, either
    #      a case insensitive regex. See the read_filters() function.
    return re.match(_filter["name"], _filename) is not None

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__filt_size(_filter, _size):
    """
        thefilehastobeadded__filt_size()
        ________________________________________________________________________

        Function used by thefilehastobeadded__filters() : check if the size of a
        file matches the filter given as a parameter.
        ________________________________________________________________________

        PARAMETERS
                o _filter        : a dict object; see documentation:selection
                o _size         : (int) file's size

        RETURNED VALUE
                the expected boolean
    """
    res = False

    filter_size = _filter["size"] # a string like ">999" : see documentation:selection

    multiple = 1
    for suffix, _multiple in CST__MULTIPLES:
        if filter_size.endswith(suffix):
            multiple = _multiple
            filter_size = filter_size[:-len(suffix)]
            break

    if multiple == 1 and not filter_size[-1].isdigit():
        raise KatalError("Can't analyse {0} in the filter. " \
                         "Available multiples are : {1}".format(filter_size,
                                                                CST__MULTIPLES))

    # beware !  the order matters (<= before <, >= before >)
    if filter_size.startswith(">="):
        if _size >= float(filter_size[2:])*multiple:
            res = True
    elif filter_size.startswith(">"):
        if _size > float(filter_size[1:])*multiple:
            res = True
    elif filter_size.startswith("<="):
        if _size <= float(filter_size[2:])*multiple:
            res = True
    elif filter_size.startswith("<"):
        if _size < float(filter_size[1:])*multiple:
            res = True
    elif filter_size.startswith("="):
        if _size == float(filter_size[1:])*multiple:
            res = True
    else:
        raise KatalError("Can't analyse {0} in the filter.".format(filter_size))

    return res

#///////////////////////////////////////////////////////////////////////////////
def welcome(_timestamp_start):
    """
        welcome()
        ________________________________________________________________________

        Display a welcome message with some very broad informations about the
        program. This function may be called before reading the configuration
        file (confer the variable CFG_PARAMETERS).

        This function is called before the opening of the log file; hence, all
        the messages are only displayed on console (see welcome_in_logfile
        function)
        ________________________________________________________________________

        PARAMETER :
                o  _timestamp_start : a datetime.datetime object

        no RETURNED VALUE

        sys.exit(-1) if the config file doesn't exist.
    """
    # first welcome message :
    strmsg = "=== {0} v.{1} " \
             "(launched at {2}) ===".format(__projectname__,
                                            __version__,
                                            _timestamp_start.strftime("%Y-%m-%d %H:%M:%S"))
    msg("="*len(strmsg),
        _consolecolor="white")
    msg(strmsg,
        _consolecolor="white")
    msg("="*len(strmsg),
        _consolecolor="white")

    # command line arguments :
    msg("  = command line arguments : {0}".format(sys.argv))

    # if the target file doesn't exist, it will be created later by main_warmup() :
    if ARGS.new is None and ARGS.downloaddefaultcfg is None:
        msg("  = target directory given as parameter : \"{0}\" " \
            "(path : \"{1}\")".format(ARGS.targetpath,
                                      normpath(ARGS.targetpath)))

        if ARGS.configfile is not None:
            msg("  = expected config file : \"{0}\" " \
                "(path : \"{1}\")".format(ARGS.configfile,
                                          normpath(ARGS.configfile)))
        else:
            msg("  * no config file specified on the command line : " \
                "let's search a config file...")

    if ARGS.off:
        msg("  = --off option detected :                                               =",
            _consolecolor="cyan")
        msg("  =                no file will be modified, no directory will be created =",
            _consolecolor="cyan")
        msg("  =                but the corresponding messages will be written in the  =",
            _consolecolor="cyan")
        msg("  =                log file.                                              =",
            _consolecolor="cyan")

#///////////////////////////////////////////////////////////////////////////////
def welcome_in_logfile(_timestamp_start):
    """
        welcome_in_logfile()
        ________________________________________________________________________

        The function writes in the log file a welcome message with some very
        broad informations about the program.

        This function has to be called after the opening of the log file.
        This function doesn't write anything on the console.

        See welcome() function for more informations since welcome() and
        welcome_in_logfile() do the same job, the first on console, the
        second in the log file.
        ________________________________________________________________________

        PARAMETER :
                o  _timestamp_start : a datetime.datetime object

        no RETURNED VALUE
    """
    msg(_msg="=== {0} v.{1} " \
        "(launched at {2}) ===".format(__projectname__,
                                       __version__,
                                       _timestamp_start.strftime("%Y-%m-%d %H:%M:%S")),
        _for_logfile=True,
        _for_console=False)

    msg("  = command line arguments : {0}".format(sys.argv),
        _for_logfile=True,
        _for_console=False)

    msg("  = target directory given as parameter : \"{0}\" " \
        "(path : \"{1}\")".format(ARGS.targetpath,
                                  normpath(ARGS.targetpath)),
        _for_logfile=True,
        _for_console=False)

#///////////////////////////////////////////////////////////////////////////////
def where_is_the_configfile():
    """
        where_is_the_configfile()
        ________________________________________________________________________

        Return the config file name from ARGS.configfile or from the paths
        returned by possible_paths_to_cfg() .
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE : ( str(filename), (int)error )

                        +-------------+------------------------------------------
                        | error value | meaning                                 |
                        +-------------+-----------------------------------------+
                        |      0      | no error : a config file has been found.|
                        +-------------+-----------------------------------------+
                        |      1      | information : can't find a config file  |
                        |             | but the --downloaddefaultcfg was set.   |
                        +-------------+-----------------------------------------+
                        |     -1      | error : can't find a config file and the|
                        |             | --downloaddefaultcfg option was NOT set |
                        +-------------+-----------------------------------------+
                        |     -2      | error : ARGS.configfile doesn't exist.  |
                        +-------------+-----------------------------------------+
    """
    configfile_name = ""

    msg_please_use_dlcfg = \
     "    ! error : can't find any config file !\n" \
     "    Use the -dlcfg/--downloaddefaultcfg option to download a default config file."

    if ARGS.configfile is None:
        # no config file given as a parameter, let's guess where it is :

        for cfg_path in possible_paths_to_cfg():
            msg("  * trying to find a config file in \"{0}\"...".format(cfg_path))

            if os.path.exists(os.path.join(cfg_path, CST__DEFAULT_CONFIGFILE_NAME)):
                msg("   ... ok a config file has been found, let's try to read it...")
                configfile_name = os.path.join(cfg_path, CST__DEFAULT_CONFIGFILE_NAME)
                break

        if configfile_name != "":
            msg("  * config file name : \"{0}\" (path : \"{1}\")".format(configfile_name,
                                                                         normpath(configfile_name)))

        else:

            if ARGS.downloaddefaultcfg is None:
                msg(msg_please_use_dlcfg,
                    _consolecolor="red")
                return ("", -1)
            else:
                msg("  ! Can't find any configuration file, but you used the " \
                    "--downloaddefaultcfg option.")
                return ("", 1)

    else:
        # A config file has been given as a parameter :
        configfile_name = ARGS.configfile

        msg("  * config file given as a parameter : \"{0}\" " \
            "(path : \"{1}\"".format(configfile_name,
                                     normpath(configfile_name)))

        if not os.path.exists(normpath(configfile_name)) and ARGS.new is None:
            msg("  ! The config file \"{0}\" (path : \"{1}\") " \
                "doesn't exist. ".format(configfile_name,
                                         normpath(configfile_name)),
                _consolecolor="red")

            if ARGS.downloaddefaultcfg is None:
                msg(msg_please_use_dlcfg,
                    _consolecolor="red")

            return ("", -2)

    return (configfile_name, 0)

#///////////////////////////////////////////////////////////////////////////////
#/////////////////////////////// STARTING POINT ////////////////////////////////
#///////////////////////////////////////////////////////////////////////////////
if __name__ == '__main__':
    main()

