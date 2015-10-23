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
        (leaving aside the doubloons), copy the selected files in a target
        directory.
        Once the target directory is filled with some files, a database is added
        to the directory to avoid future doubloons. You can add new files to
        the target directory by using Katal one more time, with a different
        source directory.
        ________________________________________________________________________

        see README.md for more documentation.
"""
# Pylint : disabling the "Using the global statement (global-statement)" warning
# pylint: disable=W0603

# Pylint : disabling the "Too many lines in module" error
# pylint: disable=C0302

# Pylint : disabling the "Use of eval" warning
# -> eval() is used in the the_file_has_to_be_added() function
# -> see below how this function is protected against malicious code execution.
# -> see AUTHORIZED_EVALCHARS
# pylint: disable=W0123

import argparse
from base64 import b64encode
from collections import namedtuple
import configparser
import ctypes
import hashlib
from datetime import datetime
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

__projectname__ = "Katal"
__author__ = "Xavier Faure (suizokukan)"
__copyright__ = "Copyright 2015, suizokukan"
__license__ = "GPL-3.0"
# see https://pypi.python.org/pypi?%3Aaction=list_classifiers
__licensepipy__ = 'License :: OSI Approved :: GNU General Public License v3 (GPLv3)'
# see https://www.python.org/dev/peps/pep-0440/ e.g 0.1.2.dev1
__version__ = "0.1.3.dev1"
__maintainer__ = "Xavier Faure (suizokukan)"
__email__ = "suizokukan @T orange D@T fr"
__status__ = "Beta"
# see https://pypi.python.org/pypi?%3Aaction=list_classifiers
__statuspypi__ = 'Development Status :: 4 - Beta'

ARGS = None # initialized by main()

# when the program verifies that there's enough free space on disk, it multiplies
# the required amount of space by these coefficient
FREESPACE_MARGIN = 1.1

DEFAULT_CONFIGFILE_NAME = "katal.ini"
DEFAULTCFGFILE_URL = "https://raw.githubusercontent.com/suizokukan/katal/master/katal/katal.ini"
DATABASE_NAME = "katal.db"
DATABASE_FULLNAME = ""  # initialized by main_warmup()
TAG_SEPARATOR = ";"  # symbol used in the database between two tags.

TIMESTAMP_BEGIN = datetime.now()  # timestamp used to compute the total time of execution.

PARAMETERS = None # see documentation:configuration file

SOURCE_PATH = ""  # initialized from the configuration file.
SOURCENAME_MAXLENGTH = 0  # initialized from the configuration file : this value
                          # fixed the way source filenames are displayed.
INFOS_ABOUT_SRC_PATH = (None, None, None)  # initialized by show_infos_about_source_path()
                                           # ((int)total_size, (int)files_number, (dict)extensions)

TARGET_PATH = ""  # initialized from the configuration file.
TARGETNAME_MAXLENGTH = 0  # initialized from the configuration file : this value
                          # fixed the way source filenames are displayed.
TARGET_DB = []  # see documentation:database; initializd by read_target_db()
KATALSYS_SUBDIR = ".katal"
TRASH_SUBSUBDIR = "trash"
TASKS_SUBSUBDIR = "tasks"
LOG_SUBSUBDIR = "logs"

# maximal length of the hashids displayed. Can't be greater than 44.
HASHID_MAXLENGTH = 20

# maximal length of the strtags displayed.
STRTAGS_MAXLENGTH = 20

LOGFILE = None  # the file descriptor, initialized by logfile_opening()
USE_LOGFILE = False  # (bool) initialized from the configuration file
LOG_VERBOSITY = "high"  # initialized from the configuration file (see documentation:logfile)

# SELECT is made of SELECTELEMENT objects, where data about the original files
# are stored.
SELECTELEMENT = namedtuple('SELECTELEMENT', ["fullname",
                                             "path",
                                             "filename_no_extens",
                                             "extension",
                                             "size",
                                             "date",
                                             "targetname",])

SELECT = {} # see documentation:selection; initialized by action__select()
SELECT_SIZE_IN_BYTES = 0  # initialized by action__select()
SIEVES = {}  # see documentation:selection; initialized by read_sieves()

# date's string format, e.g. "2015-09-17 20:01"
DATETIME_FORMAT = "%Y-%m-%d %H:%M"
DATETIME_FORMAT_LENGTH = 16

# this minimal subset of characters are the only characters to be used in the
# eval() function. Other characters are forbidden to avoid malicious code execution.
# keywords an symbols : sieve, parentheses, and, or, not, xor, True, False
#                       space, &, |, ^, (, ), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9
AUTHORIZED_EVALCHARS = " TFadlsievruxnot0123456789&|^()"

# string used to create the database :
SQL__CREATE_DB = 'CREATE TABLE dbfiles ' \
                 '(hashid varchar(44) PRIMARY KEY UNIQUE, name TEXT UNIQUE, ' \
                 'sourcename TEXT, sourcedate INTEGER, strtags TEXT)'

################################################################################
class ProjectError(BaseException):
    """
        ProjectError class

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

        Add the source files to the target path.
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                (int) 0 if success, -1 if an error occured.
    """
    msg("  = copying data =")

    db_connection = sqlite3.connect(DATABASE_FULLNAME)
    db_cursor = db_connection.cursor()

    if get_disk_free_space(TARGET_PATH) < SELECT_SIZE_IN_BYTES*FREESPACE_MARGIN:
        msg("    ! Not enough space on disk. Stopping the program.")
        # returned value : -1 = error
        return -1

    files_to_be_added = []
    len_select = len(SELECT)
    for index, hashid in enumerate(SELECT):

        complete_source_filename = SELECT[hashid].fullname
        target_name = os.path.join(normpath(TARGET_PATH), SELECT[hashid].targetname)

        sourcedate = datetime.utcfromtimestamp(os.path.getmtime(complete_source_filename))
        sourcedate = sourcedate.replace(second=0, microsecond=0)

        # converting the datetime object in epoch value (=the number of seconds from 1970-01-01 :
        sourcedate -= datetime(1970, 1, 1)
        sourcedate = sourcedate.total_seconds()

        msg("    ... ({0}/{1}) copying \"{2}\" to \"{3}\" .".format(index+1,
                                                                    len_select,
                                                                    complete_source_filename,
                                                                    target_name))
        if not ARGS.off:
            shutil.copyfile(complete_source_filename, target_name)
            os.utime(target_name, (sourcedate, sourcedate))

        files_to_be_added.append((hashid,
                                  target_name,
                                  complete_source_filename,
                                  sourcedate,
                                  ""))

    msg("    = all files have been copied, let's update the database... =")

    try:
        if not ARGS.off:
            db_cursor.executemany('INSERT INTO dbfiles VALUES (?,?,?,?,?)', files_to_be_added)

    except sqlite3.IntegrityError as exception:
        msg("!!! An error occured while writing the database : "+str(exception))
        msg("!!! files_to_be_added : ")
        for file_to_be_added in files_to_be_added:
            msg("     ! hashid={0}; name={1}; sourcename={2}; " \
                "sourcedate={3}; strtags={4}".format(*file_to_be_added))
        raise ProjectError("An error occured while writing the database : "+str(exception))

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
    msg("  = let's add the string tag \"{0}\" to {1}".format(_tag, _to))
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

    if not os.path.exists(normpath(DATABASE_FULLNAME)):
        msg("    ! no database found.")
        return

    db_connection = sqlite3.connect(DATABASE_FULLNAME)
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    files_to_be_rmved_from_the_db = []  # hashid of the files
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        if not os.path.exists(os.path.join(normpath(TARGET_PATH), db_record["name"])):
            files_to_be_rmved_from_the_db.append(db_record["hashid"])
            msg("    o about to remove \"{0}\" " \
                "from the database".format(os.path.join(normpath(TARGET_PATH),
                                                        db_record["name"])))

    if len(files_to_be_rmved_from_the_db) == 0:
        msg("    ! no file to be removed : the database is ok.")
    else:
        for hashid in files_to_be_rmved_from_the_db:
            if not ARGS.off:
                msg("    o removing \"{0}\" record " \
                    "from the database".format(hashid))
                db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))
                db_connection.commit()

    db_connection.close()
    if not ARGS.off:
        msg("    o ... done : remove {0} " \
            "file(s) from the database".format(len(files_to_be_rmved_from_the_db)))

#///////////////////////////////////////////////////////////////////////////////
def action__downloadefaultcfg(newname=DEFAULT_CONFIGFILE_NAME):
    """
        action__downloadefaultcfg()
        ________________________________________________________________________

        Download the default configuration file and give to it the name "newname"
        ________________________________________________________________________

        PARAMETER :
            (str) newname : the new name of the downloaded file

        RETURNED VALUE :
            (bool) success
    """
    msg("  = downloading the default configuration file =")
    msg("  ... downloading {0} from {1}".format(newname, DEFAULTCFGFILE_URL))

    try:
        if not ARGS.off:
            with urllib.request.urlopen(DEFAULTCFGFILE_URL) as response, \
                 open(newname, 'wb') as out_file:
                shutil.copyfileobj(response, out_file)
        return True

    except urllib.error.URLError as exception:
        msg("  ! An error occured : "+str(exception))
        return False

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
def action__new(targetname):
    """
        action__new()
        ________________________________________________________________________

        Create a new target directory
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    msg("  = about to create a new target directory " \
        "named \"{0}\" (path : \"{1}\")".format(targetname,
                                                normpath(targetname)))
    if os.path.exists(normpath(targetname)):
        msg("  ! can't go further : the directory already exists.")
        return

    if not ARGS.off:
        os.mkdir(normpath(targetname))
        os.mkdir(os.path.join(normpath(targetname), KATALSYS_SUBDIR))
        os.mkdir(os.path.join(normpath(targetname), KATALSYS_SUBDIR, TRASH_SUBSUBDIR))
        os.mkdir(os.path.join(normpath(targetname), KATALSYS_SUBDIR, TASKS_SUBSUBDIR))
        os.mkdir(os.path.join(normpath(targetname), KATALSYS_SUBDIR, LOG_SUBSUBDIR))

    if not ARGS.mute:
        answer = \
            input("\nDo you want to download the default config file " \
                  "into the expected directory ? (y/N) ")

        if answer in ("y", "yes"):
            if action__downloadefaultcfg(os.path.join(normpath(targetname),
                                                      KATALSYS_SUBDIR,
                                                      DEFAULT_CONFIGFILE_NAME)):
                msg("  ... done.")
            else:
                print("  ! A problem occured : " \
                      "the creation of the target directory has been aborted.")

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
    msg("  = copying the current target directory into a new one =")
    msg("    o from {0} (path : \"{1}\")".format(SOURCE_PATH,
                                                 normpath(SOURCE_PATH)))

    msg("    o to   {0} (path : \"{1}\")".format(_newtargetpath,
                                                 normpath(_newtargetpath)))

    to_configfile = os.path.join(_newtargetpath,
                                 KATALSYS_SUBDIR,
                                 DEFAULT_CONFIGFILE_NAME)
    msg("    o trying to read dest config file {0} " \
        "(path : \"{1}\") .".format(to_configfile,
                                    normpath(to_configfile)))
    dest_params = read_parameters_from_cfgfile(normpath(to_configfile))

    if dest_params is None:
        msg("    ! can't read the dest config file !")
        return

    msg("    o config file found and read (ok)")
    msg("    o new filenames' format : " \
        "{0}".format(dest_params["target"]["name of the target files"]))

    new_db = os.path.join(normpath(_newtargetpath), KATALSYS_SUBDIR, DATABASE_NAME)
    if not ARGS.off:
        if os.path.exists(new_db):
            # let's delete the new database :
            os.remove(new_db)

    # let's compute the new names :
    olddb_connection = sqlite3.connect(DATABASE_FULLNAME)
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
        ________________________________________________________________________

        PARAMETER :
                o _olddb_cursor         : cursor to the source database
                o _dest_params          : an object returned by read_parameters_from_cfgfile(),
                                          like PARAMETERS
                o _newtargetpath        : (str) path to the new target directory.

        RETURNED VALUE :
                (files, (int)number of anomalies)

                files : a dict hashid::(source name, new name, source date, source strtags)
    """
    files = dict()      # dict to be returned.
    filenames = set()   # to be used to avoir doubloons.

    anomalies_nbr = 0
    for index, olddb_record in enumerate(_olddb_cursor.execute('SELECT * FROM dbfiles')):
        fullname = normpath(os.path.join(SOURCE_PATH, olddb_record["name"]))
        filename_no_extens, extension = get_filename_and_extension(fullname)

        size = os.stat(fullname).st_size
        date = olddb_record["sourcedate"]
        new_name = \
            create_target_name(_parameters=_dest_params,
                               _hashid=olddb_record["hashid"],
                               _filename_no_extens=filename_no_extens,
                               _path=olddb_record["sourcename"],
                               _extension=extension,
                               _size=size,
                               _date=datetime.utcfromtimestamp(date).strftime(DATETIME_FORMAT),
                               _database_index=index)
        new_name = normpath(os.path.join(_newtargetpath, new_name))
        strtags = olddb_record["strtags"]

        msg("      o {0} : {1} would be copied as {2}".format(olddb_record["hashid"],
                                                              olddb_record["name"],
                                                              new_name))

        if new_name in filenames:
            msg("      ! anomaly : ancient file {1} should be renamed as {0} " \
                "but this name would have been already created in the new target directory ! " \
                "".format(new_name, fullname))
            msg("        Two different files from the ancient target directory " \
                "can't bear the same name in the new target directory !")
            anomalies_nbr += 1
        elif os.path.exists(new_name):
            msg("      ! anomaly : ancient file {1} should be renamed as {0} " \
                "but this name already exists in new target directory !".format(new_name, fullname))
            anomalies_nbr += 1
        else:
            files[olddb_record["hashid"]] = (fullname, new_name, date, strtags)
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
            newdb_cursor.execute(SQL__CREATE_DB)

        for index, futurefile_hashid in enumerate(_files):
            futurefile = _files[futurefile_hashid]
            file_to_be_added = (futurefile_hashid,      # hashid
                                futurefile[1],          # new name
                                futurefile[0],          # sourcename
                                futurefile[2],          # sourcedate
                                futurefile[3])          # tags

            strdate = datetime.utcfromtimestamp(futurefile[2]).strftime(DATETIME_FORMAT)
            msg("    o ({0}/{1}) adding a file in the new database".format(index+1, len(_files)))
            msg("      o hashid : {0}".format(futurefile_hashid))
            msg("      o source name : {0}".format(futurefile[0]))
            msg("      o desti. name : {0}".format(futurefile[1]))
            msg("      o source date : {0}".format(strdate))
            msg("      o tags : \"{0}\"".format(futurefile[3]))

            newdb_cursor.execute('INSERT INTO dbfiles VALUES (?,?,?,?,?)', file_to_be_added)
            newdb_connection.commit()

    except sqlite3.IntegrityError as exception:
        msg("!!! An error occured while writing the new database : "+str(exception))
        raise ProjectError("An error occured while writing the new database : "+str(exception))

    newdb_connection.close()

    # let's copy the files :
    for index, futurefile_hashid in enumerate(_files):
        futurefile = _files[futurefile_hashid]
        old_name, new_name = futurefile[0], futurefile[1]

        msg("    o ({0}/{1}) copying \"{2}\" as \"{3}\"".format(index+1, len(_files),
                                                                old_name, new_name))
        shutil.copyfile(old_name, new_name)

    msg("    ... done")

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

    if not os.path.exists(normpath(DATABASE_FULLNAME)):
        msg("    ! no database found.")
    else:
        db_connection = sqlite3.connect(DATABASE_FULLNAME)
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        files_to_be_removed = []    # list of (hashid, name)
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if db_record["strtags"] == "":
                files_to_be_removed.append((db_record["hashid"], db_record["name"]))

        if len(files_to_be_removed) == 0:
            msg("   ! no files to be removed.")
        else:
            for hashid, name in files_to_be_removed:
                msg("   o removing {0} from the database and from the target path".format(name))
                if not ARGS.off:
                    # removing the file from the target directory :
                    shutil.move(os.path.join(normpath(TARGET_PATH), name),
                                os.path.join(normpath(TARGET_PATH),
                                             KATALSYS_SUBDIR, TRASH_SUBSUBDIR, name))
                    # let's remove the file from the database :
                    db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))

        db_connection.commit()
        db_connection.close()

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
                "in the config file. Please wait... =")
    msg("  o sieves :")
    for sieve_index in SIEVES:
        msg("    o sieve #{0} : {1}".format(sieve_index,
                                            SIEVES[sieve_index]))
    msg("  o file list :")

    # let's initialize SELECT and SELECT_SIZE_IN_BYTES :
    number_of_discarded_files = fill_select()

    msg("    o size of the selected files : {0}".format(size_as_str(SELECT_SIZE_IN_BYTES)))

    if len(SELECT) == 0:
        msg("    ! no file selected ! " \
            "You have to modify the config file to get some files selected.")
    else:
        ratio = len(SELECT)/(len(SELECT)+number_of_discarded_files)*100.0
        msg("    o number of selected files " \
                  "(after discarding {1} file(s)) : {0}, " \
                  "{2:.2f}% of the source files.".format(len(SELECT),
                                                         number_of_discarded_files,
                                                         ratio))

    # let's check that the target path has sufficient free space :
    available_space = get_disk_free_space(TARGET_PATH)
    if available_space > SELECT_SIZE_IN_BYTES*FREESPACE_MARGIN:
        size_ok = "ok"
    else:
        size_ok = "!!! problem !!!"
    msg("    o required space : {0}; " \
        "available space on disk : {1} ({2})".format(size_as_str(SELECT_SIZE_IN_BYTES),
                                                     size_as_str(available_space),
                                                     size_ok))

    # if there's no --add option, let's give some examples of the target names :
    if not ARGS.add:
        example_index = 0
        for hashid in SELECT:

            complete_source_filename = SELECT[hashid].fullname

            target_name = os.path.join(normpath(TARGET_PATH), SELECT[hashid].targetname)

            msg("    o e.g. ... \"{0}\" " \
                "would be copied as \"{1}\" .".format(complete_source_filename,
                                                      target_name))

            example_index += 1

            if example_index > 5:
                break

#///////////////////////////////////////////////////////////////////////////////
def action__rmtags(_to):
    """
        action__rmtags()
        ________________________________________________________________________

        Remove the string tag(s) in the target directory, overwriting ancient tags.
        ________________________________________________________________________

        PARAMETERS
                o _to           : (str) a regex string describing what files are
                                  concerned
    """
    msg("  = let's remove the string tags in {0}".format(_to))
    action__setstrtags(_strtags="", _to=_to)

#///////////////////////////////////////////////////////////////////////////////
def action__setstrtags(_strtags, _to):
    """
        action__setstrtags()
        ________________________________________________________________________

        Set the string tag(s) in the target directory, overwriting ancient tags.
        ________________________________________________________________________

        PARAMETERS
                o _strtags      : (str) the new string tags
                o _to           : (str) a regex string describing what files are
                                  concerned
    """
    msg("  = let's apply the string tag \"{0}\" to {1}".format(_strtags, _to))
    modify_the_tag_of_some_files(_tag=_strtags, _to=_to, _mode="set")

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
    if not os.path.exists(os.path.join(normpath(TARGET_PATH), _filename)):
        msg("    ! can't find \"{0}\" file on disk.".format(_filename))
        return -1

    if not os.path.exists(normpath(DATABASE_FULLNAME)):
        msg("    ! no database found.")
        return -3
    else:
        db_connection = sqlite3.connect(DATABASE_FULLNAME)
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        filename_hashid = None
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if db_record["name"] == os.path.join(normpath(TARGET_PATH), _filename):
                filename_hashid = db_record["hashid"]

        if filename_hashid is None:
            msg("    ! can't find \"{0}\" file in the database.".format(_filename))
            res = -2
        else:
            if not ARGS.off:
                # let's remove _filename from the target directory :
                shutil.move(os.path.join(normpath(TARGET_PATH), _filename),
                            os.path.join(normpath(TARGET_PATH),
                                         KATALSYS_SUBDIR, TRASH_SUBSUBDIR, _filename))

                # let's remove _filename from the database :
                db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (filename_hashid,))

            res = 0  # success.

        db_connection.commit()
        db_connection.close()

        msg("    ... done")
        return res

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
        raise ProjectError("--select and --add can't be used simultaneously")

    # --setstrtags must be used with --to :
    if ARGS.setstrtags and not ARGS.to:
        raise ProjectError("please use --to in combination with --setstrtags")

    # --addtag must be used with --to :
    if ARGS.addtag and not ARGS.to:
        raise ProjectError("please use --to in combination with --addtag")

    # --rmtags must be used with --to :
    if ARGS.rmtags and not ARGS.to:
        raise ProjectError("please use --to in combination with --rmtags")

#///////////////////////////////////////////////////////////////////////////////
def create_subdirs_in_target_path():
    """
        create_subdirs_in_target_path()
        ________________________________________________________________________

        Create the expected subdirectories in TARGET_PATH .
        ________________________________________________________________________

        no PARAMETERS, no RETURNED VALUE
    """
    # (str)name for the message, (str)full path :
    for name, \
        fullpath in (("target", TARGET_PATH),
                     ("system", os.path.join(normpath(TARGET_PATH),
                                             KATALSYS_SUBDIR)),
                     ("trash", os.path.join(normpath(TARGET_PATH),
                                            KATALSYS_SUBDIR, TRASH_SUBSUBDIR)),
                     ("log", os.path.join(normpath(TARGET_PATH),
                                          KATALSYS_SUBDIR, LOG_SUBSUBDIR)),
                     ("tasks", os.path.join(normpath(TARGET_PATH),
                                            KATALSYS_SUBDIR, TASKS_SUBSUBDIR))):
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
        stored in SELECT. The function reads the string stored in
        _parameters["target"]["name of the target files"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)
        ________________________________________________________________________

        PARAMETERS
                o _parameters                   : an object returned by
                                                  read_parameters_from_cfgfile(),
                                                  like PARAMETERS
                o _hashid                       : (str)
                o _filename_no_extens           : (str)
                o _path                         : (str
                o _extension                    : (str)
                o _size                         : (int)
                o _date                         : (str) see DATETIME_FORMAT
                o _database_index               : (int)

        RETURNED VALUE
                the expected string
    """
    target_name = _parameters["target"]["name of the target files"]

    target_name = target_name.replace("HASHID", _hashid)

    target_name = target_name.replace("SOURCENAME_WITHOUT_EXTENSION2", _filename_no_extens)
    target_name = target_name.replace("SOURCENAME_WITHOUT_EXTENSION", _filename_no_extens)

    target_name = target_name.replace("SOURCE_PATH2", _path)
    target_name = target_name.replace("SOURCE_PATH", _path)

    target_name = target_name.replace("SOURCE_EXTENSION2", remove_illegal_characters(_extension))
    target_name = target_name.replace("SOURCE_EXTENSION", _extension)

    target_name = target_name.replace("SIZE", str(_size))

    target_name = target_name.replace("DATE2", remove_illegal_characters(_date))

    target_name = target_name.replace("INTTIMESTAMP",
                                      str(int(datetime.strptime(_date,
                                                                DATETIME_FORMAT).timestamp())))

    target_name = target_name.replace("HEXTIMESTAMP",
                                      hex(int(datetime.strptime(_date,
                                                                DATETIME_FORMAT).timestamp()))[2:])

    target_name = target_name.replace("DATABASE_INDEX",
                                      remove_illegal_characters(str(_database_index)))

    return target_name

#///////////////////////////////////////////////////////////////////////////////
def eval_sieve_for_a_file(_sieve, _filename, _size, _date):
    """
        eval_sieve_for_a_file()
        ________________________________________________________________________

        Eval a file according to a sieve and answers the following question :
        does the file matches what is described in the sieve ?
        ________________________________________________________________________

        PARAMETERS
                o _sieve        : a dict, see documentation:select
                o _filename     : (str) file's name
                o _size         : (int) file's size, in bytes.
                o _date         : (str)file's date

        RETURNED VALUE
                a boolean, giving the expected answer
    """
    res = True

    if res and "name" in _sieve:
        res = the_file_has_to_be_added__name(_sieve, _filename)
    if res and "size" in _sieve:
        res = the_file_has_to_be_added__size(_sieve, _size)
    if res and "date" in _sieve:
        res = the_file_has_to_be_added__date(_sieve, _date)

    return res

#///////////////////////////////////////////////////////////////////////////////
def fill_select(_debug_datatime=None):
    """
        fill_select()
        ________________________________________________________________________

        Fill SELECT and SELECT_SIZE_IN_BYTES from the files stored in
        SOURCE_PATH. This function is used by action__select() .
        ________________________________________________________________________

        PARAMETERS
                o  _debug_datatime : None (normal value) or a dict of DATETIME_FORMAT
                                     strings if in debug/test mode.

        RETURNED VALUE
                (int) the number of discarded files
    """
    global SELECT, SELECT_SIZE_IN_BYTES

    SELECT = {}  # see the SELECT format in the documentation:selection
    SELECT_SIZE_IN_BYTES = 0
    number_of_discarded_files = 0

    # these variables will be used by fill_select__checks() too.
    prefix = ""
    fullname = ""

    file_index = 0  # number of the current file in the source directory.
    for dirpath, _, filenames in os.walk(normpath(SOURCE_PATH)):
        for filename in filenames:
            file_index += 1
            fullname = os.path.join(normpath(dirpath), filename)
            size = os.stat(fullname).st_size
            if _debug_datatime is None:
                time = datetime.utcfromtimestamp(os.path.getmtime(normpath(fullname)))
                time = time.replace(second=0, microsecond=0)
            else:
                time = datetime.strptime(_debug_datatime[fullname], DATETIME_FORMAT)

            filename_no_extens, extension = get_filename_and_extension(normpath(filename))

	    # if we know the total amount of files to be selected (see the --infos option),
	    # we can add the percentage done :
            prefix = ""
            if INFOS_ABOUT_SRC_PATH[1] is not None and INFOS_ABOUT_SRC_PATH[1] != 0:
                prefix = "[{0:.4f}%]".format(file_index/INFOS_ABOUT_SRC_PATH[1]*100.0)

            res = the_file_has_to_be_added(filename, size, time)
            if not res:
                number_of_discarded_files += 1

                msg("    - {0} discarded \"{1}\" " \
                    ": incompatibility with the sieves".format(prefix, fullname),
                    _important_msg=False)
            else:
                _hash = hashfile64(fullname)

                # is filename already stored in <TARGET_DB> ?
                if _hash not in TARGET_DB and _hash not in SELECT:
                    # no, so we may add _hash to SELECT...
                    _targetname = create_target_name(_parameters=PARAMETERS,
                                                     _hashid=_hash,
                                                     _filename_no_extens=filename_no_extens,
                                                     _path=dirpath,
                                                     _extension=extension,
                                                     _size=size,
                                                     _date=time.strftime(DATETIME_FORMAT),
                                                     _database_index=len(TARGET_DB) + len(SELECT))

                    SELECT[_hash] = SELECTELEMENT(fullname=fullname,
                                                  path=dirpath,
                                                  filename_no_extens=filename_no_extens,
                                                  extension=extension,
                                                  size=size,
                                                  date=time.strftime(DATETIME_FORMAT),
                                                  targetname=_targetname)

                    msg("    + {0} selected {1} (file selected #{2})".format(prefix,
                                                                             fullname,
                                                                             len(SELECT)),
                        _important_msg=False)

                    SELECT_SIZE_IN_BYTES += os.stat(normpath(fullname)).st_size
                else:
                    res = False
                    number_of_discarded_files += 1

                    msg("    - {0} (similar hashid) " \
                        " discarded \"{1}\"".format(prefix, fullname),
                        _important_msg=False)

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
                    stored in the target path :
        ________________________________________________________________________

        no PARAMETER
                o _number_of_discarded_files    : (int) see fill_select()
                o _prefix                       : (str) see fill_select()
                o _fullname                     : (str) see fill_select()

        RETURNED VALUE
                (int) the number of discarded files
    """
    # (1) future filename's can't be in conflict with another file in SELECT
    to_be_discarded = []        # a list of hash.
    for (selectedfile_hash1, selectedfile_hash2) in itertools.combinations(SELECT, 2):

        if SELECT[selectedfile_hash1].targetname == SELECT[selectedfile_hash2].targetname:
            msg("    ! {0} discarded \"{1}\" : target filename \"{2}\" would be used " \
                "two times for two different files !".format(_prefix,
                                                             _fullname,
                                                             SELECT[selectedfile_hash2].targetname))

            to_be_discarded.append(selectedfile_hash2)

    # (2) future filename's can't be in conflict with another file already
    # stored in the target path :
    for selectedfile_hash in SELECT:
        if os.path.exists(os.path.join(normpath(TARGET_PATH),
                                       SELECT[selectedfile_hash].targetname)):
            msg("    ! {0} discarded \"{1}\" : target filename \"{2}\" already " \
                "exists in the target path !".format(_prefix,
                                                     _fullname,
                                                     SELECT[selectedfile_hash].targetname))

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
                                        ending))

        for _hash in to_be_discarded:
            # e.g. , _hash may have discarded two times (same target name + file
            # already present on disk), hence the following condition :
            if _hash in SELECT:
                del SELECT[_hash]
                _number_of_discarded_files += 1

    return _number_of_discarded_files

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
    if platform.system() == 'Windows':
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
    filename_no_extens, extension = os.path.splitext(_path)

    # the extension can't begin with a dot.
    if extension.startswith("."):
        extension = extension[1:]

    return filename_no_extens, extension

#///////////////////////////////////////////////////////////////////////////////
def goodbye():
    """
        goodbye()
        ________________________________________________________________________

        If not in quiet mode (see --quiet option), display a goodbye message.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    if ARGS.quiet:
        return

    msg("=== exit (stopped at {0}; " \
        "total duration time : {1}) ===".format(datetime.now().strftime(DATETIME_FORMAT),
                                                datetime.now() - TIMESTAMP_BEGIN))

#///////////////////////////////////////////////////////////////////////////////
def hashfile64(_filename):
    """
        hashfile64()
        ________________________________________________________________________

        return the footprint of a file, encoded with the base 64.
        ________________________________________________________________________

        PARAMETER
                o _filename : (str) file's name

        RETURNED VALUE
                the expected string. If you use sha256 as a hasher, the
                resulting string will be 44 bytes long. E.g. :
                        "YLkkC5KqwYvb3F54kU7eEeX1i1Tj8TY1JNvqXy1A91A"
    """
    # hasher used by the hashfile64() function. The SHA256 is a good choice;
    # if you change the hasher, please modify the way the hashids are displayed
    # (see the action__informations() function)
    hasher = hashlib.sha256()

    with open(_filename, "rb") as afile:
        buf = afile.read(65536)
        while len(buf) > 0:
            hasher.update(buf)
            buf = afile.read(65536)
    return b64encode(hasher.digest()).decode()

#///////////////////////////////////////////////////////////////////////////////
def logfile_opening():
    """
        logfile_opening()
        ________________________________________________________________________

        Open the log file and return the result of the called to open().
        If the ancient logfile exists, it is renamed to avoid its overwriting.
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                the _io.BufferedReader object returned by the call to open()
    """
    fullname = os.path.join(KATALSYS_SUBDIR, LOG_SUBSUBDIR, PARAMETERS["log file"]["name"])

    if PARAMETERS["log file"]["overwrite"] == "True":
        # overwrite :
        log_mode = "w"

        if os.path.exists(normpath(fullname)):
            shutil.copyfile(fullname,
                            os.path.join(KATALSYS_SUBDIR, LOG_SUBSUBDIR,
                                         "oldlogfile_" + \
                                         PARAMETERS["log file"]["name"] + \
                                         datetime.strftime(datetime.now(), "%Y%m%d%H%M%S")))
    else:
        # let's append :
        log_mode = "a"

    return open(fullname, log_mode)

#///////////////////////////////////////////////////////////////////////////////
def main():
    """
        main()
        ________________________________________________________________________

        Main entry point.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE

        o  sys.exit(-1) is called if the config file is ill-formed.
        o  sys.exit(-2) is called if a ProjectError exception is raised
        o  sys.exit(-3) is called if another exception is raised
    """
    global ARGS

    try:
        ARGS = read_command_line_arguments()
        check_args()

        if ARGS.targetinfos:
            ARGS.quiet = True

        welcome()
        main_warmup()
        main_actions_tags()
        main_actions()

        goodbye()

        if USE_LOGFILE:
            LOGFILE.close()

    except ProjectError as exception:
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

    if ARGS.hashid:
        show_hashid_of_a_file(ARGS.hashid)

    if ARGS.targetkill:
        action__target_kill(ARGS.targetkill)

    if ARGS.select:
        read_target_db()
        read_sieves()
        action__select()

        if not ARGS.mute and len(SELECT) > 0:
            answer = \
                input("\nDo you want to add the selected " \
                      "files to the target dictionary (\"{0}\") ? (y/N) ".format(TARGET_PATH))

            if answer in ("y", "yes"):
                action__add()
                action__infos()

    if ARGS.add:
        read_target_db()
        read_sieves()
        action__select()
        action__add()
        action__infos()

    if ARGS.new:
        action__new(ARGS.new)

    if ARGS.rebase:
        action__rebase(ARGS.rebase)

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

    if ARGS.setstrtags:
        action__setstrtags(ARGS.setstrtags, ARGS.to)

    if ARGS.addtag:
        action__addtag(ARGS.addtag, ARGS.to)

    if ARGS.rmtags:
        action__rmtags(ARGS.to)

#///////////////////////////////////////////////////////////////////////////////
def main_warmup():
    """
        main_warmup()
        ________________________________________________________________________

        Initialization
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE

        o  sys.exit(-1) is called if the config file is ill-formed.
    """
    global PARAMETERS, LOGFILE, DATABASE_FULLNAME

    if ARGS.downloaddefaultcfg:
        if not action__downloadefaultcfg():
            msg("  ! The default configuration file couldn't be downloaded !")

    configfile_name = ARGS.configfile
    if ARGS.configfile is None:
        configfile_name = os.path.join(normpath("."),
                                       normpath(ARGS.targetpath),
                                       KATALSYS_SUBDIR,
                                       DEFAULT_CONFIGFILE_NAME)
        msg("  * config file name : \"{0}\" (path : \"{1}\")".format(configfile_name,
                                                                     normpath(configfile_name)))

    if not os.path.exists(normpath(configfile_name)) and ARGS.new is None:
        msg("  ! The config file \"{0}\" (path : \"{1}\") " \
            "doesn't exist. ".format(configfile_name,
                                     normpath(configfile_name)))
        msg("    Use the -ddcfg/--downloaddefaultcfg option to download a default config file and ")
        msg("    move this downloaded file into the target/.katal/ directory .")

    elif ARGS.new is None:
        PARAMETERS = read_parameters_from_cfgfile(configfile_name)
        if PARAMETERS is None:
            sys.exit(-1)
        else:
            msg("    ... config file found and read (ok)")

        DATABASE_FULLNAME = os.path.join(normpath(TARGET_PATH), KATALSYS_SUBDIR, DATABASE_NAME)

        # list of the expected directories : if one directory is missing, let's create it.
        create_subdirs_in_target_path()

        if USE_LOGFILE:
            LOGFILE = logfile_opening()
            welcome_in_logfile()

        if TARGET_PATH == SOURCE_PATH:
            msg("  ! warning : " \
                "source path and target path have the same value ! (\"{0}\")".format(TARGET_PATH))

        if not ARGS.quiet:
            msg("  = source directory : \"{0}\" (path : \"{1}\")".format(SOURCE_PATH,
                                                                         normpath(SOURCE_PATH)))

        if ARGS.infos:
            action__infos()

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
    if not os.path.exists(normpath(DATABASE_FULLNAME)):
        msg("    ! no database found.")
    else:
        db_connection = sqlite3.connect(DATABASE_FULLNAME)
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        files_to_be_modified = []       # a list of (hashids, name)
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if fnmatch.fnmatch(db_record["name"], os.path.join(normpath(TARGET_PATH), _to)):
                files_to_be_modified.append((db_record["hashid"], db_record["name"]))

        if len(files_to_be_modified) == 0:
            msg("    * no files match the given name(s) given as a parameter.")
        else:
            # let's apply the tag(s) to the <files_to_be_modified> :
            for hashid, filename in files_to_be_modified:

                msg("    o applying the string tag \"{0}\" to {1}.".format(_tag, filename))

                if ARGS.off:
                    pass

                elif _mode == "set":
                    sqlorder = 'UPDATE dbfiles SET strtags=? WHERE hashid=?'
                    db_connection.execute(sqlorder, (_tag, hashid))

                elif _mode == "append":
                    sqlorder = 'UPDATE dbfiles SET strtags = strtags || \"{0}{1}\" ' \
                               'WHERE hashid=\"{2}\"'.format(TAG_SEPARATOR, _tag, hashid)
                    db_connection.executescript(sqlorder)

                else:
                    raise ProjectError("_mode argument \"{0}\" isn't known".format(_mode))

            db_connection.commit()

        db_connection.close()

#///////////////////////////////////////////////////////////////////////////////
def msg(_msg, _for_console=True, _for_logfile=True, _important_msg=True):
    """
        msg()
        ________________________________________________________________________

        Display a message on console, write the same message in the log file
        The messagfe isn't displayed on console if ARGS.mute has been set to
        True (see --mute argument)
        ________________________________________________________________________

        PARAMETERS
                o _msg          : (str) the message to be written
                o _for_console  : (bool) authorization to write on console
                o _for_logfile  : (bool) authorization to write in the log file
                o _important_msg: (bool) if False, will be printed only if
                                  LOG_VERBOSITY is set to "high" .

        no RETURNED VALUE
    """
    if _important_msg is True and LOG_VERBOSITY == "low":
        return

    # first to the console : otherwise, if an error occurs by writing to the log
    # file, it would'nt possible to read the message.
    if not ARGS.mute and _for_console:
        print(_msg)

    if USE_LOGFILE and _for_logfile and LOGFILE is not None:
        LOGFILE.write(_msg+"\n")

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
    parser = argparse.ArgumentParser(description="{0} v. {1}".format(__projectname__, __version__),
                                     epilog="by suizokukan AT orange DOT fr",
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('--add',
                        action="store_true",
                        help="select files according to what is described " \
                             "in the configuration file " \
                             "then add them to the target directory. " \
                             "This option can't be used with the --select one." \
                             "If you want more informations about the process, please " \
                             "use this option in combination with --infos .")

    parser.add_argument('--addtag',
                        type=str,
                        help="Add a tag to some file(s) in combination " \
                             "with the --to option. ")

    parser.add_argument('-c', '--configfile',
                        type=str,
                        help="config file, e.g. config.ini")

    parser.add_argument('--cleandbrm',
                        action="store_true",
                        help="Remove from the database the missing files in the target path.")

    parser.add_argument('-ddcfg', '--downloaddefaultcfg',
                        action="store_true",
                        help="Download the default config file and overwrite the file having " \
                             "the same name. This is done before the script reads the parameters " \
                             "in the config file")

    parser.add_argument('--hashid',
                        type=str,
                        help="return the hash id of the given file")

    parser.add_argument('--infos',
                        action="store_true",
                        help="display informations about the source directory " \
                             "given in the configuration file. Help the --select/--add " \
                             "options to display more informations about the process : in " \
			     "this case, the --infos will be executed before --select/--add")

    parser.add_argument('-m', '--mute',
                        action="store_true",
                        help="no output to the console; no question asked on the console")

    parser.add_argument('-n', '--new',
                        type=str,
                        help="create a new target directory")

    parser.add_argument('--off',
                        action="store_true",
                        help="don't write anything into the target directory or into " \
                             "the database, except into the current log file. " \
                             "Use this option to simulate an operation : you get the messages " \
                             "but no file is modified on disk, no directory is created.")

    parser.add_argument('-q', '--quiet',
                        action="store_true",
                        help="no welcome/goodbye/informations about the parameters/ messages " \
                             "on console")

    parser.add_argument('--rebase',
                        type=str,
                        help="copy the current target directory into a new one : you " \
                             "rename the files in the target directory and in the database. " \
                             "First, use the --new option to create a new target directory, " \
                             "modify the .ini file of the new target directory " \
                             "(modify [target]name of the target files), " \
                             "then use --rebase with the name of the new target directory")

    parser.add_argument('--rmnotags',
                        action="store_true",
                        help="remove all files without a tag")

    parser.add_argument('--rmtags',
                        action="store_true",
                        help="remove all the tags of some file(s) in combination " \
                             "with the --to option. ")

    parser.add_argument('-s', '--select',
                        action="store_true",
                        help="select files according to what is described " \
                             "in the configuration file " \
                             "without adding them to the target directory. " \
                             "This option can't be used with the --add one." \
                     "If you want more informations about the process, please " \
                 "use this option in combination with --infos .")

    parser.add_argument('--setstrtags',
                        type=str,
                        help="give the string tag to some file(s) in combination " \
                             "with the --to option. " \
                             "Overwrite the ancient string tag.")

    parser.add_argument('--targetpath',
                        type=str,
                        default=".",
                        help="target path, usually '.'")

    parser.add_argument('-ti', '--targetinfos',
                        action="store_true",
                        help="display informations about the target directory in --quiet mode")

    parser.add_argument('-tk', '--targetkill',
                        type=str,
                        help="kill (=move to the trash directory) one file from " \
                             "the target directory." \
                             "DO NOT GIVE A PATH, just the file's name, " \
                             "without the path to the target directory ")

    parser.add_argument('--to',
                        type=str,
                        help="give the name of the file(s) concerned by --setstrtags. " \
                        "wildcards accepted; e.g. to select all .py files, use '*.py' . " \
                        "Please DON'T ADD the path to the target directory, only the filenames")

    parser.add_argument('--version',
                        action='version',
                        version="{0} v. {1}".format(__projectname__, __version__),
                        help="show the version and exit")

    return parser.parse_args()

#///////////////////////////////////////////////////////////////////////////////
def read_parameters_from_cfgfile(_configfile_name):
    """
        read_parameters_from_cfgfile()
        ________________________________________________________________________

        Read the configfile and return the parser or None if an error occured.
        ________________________________________________________________________

        PARAMETER
                o _configfile_name       : (str) config file name (e.g. katal.ini)

        RETURNED VALUE
                None if an error occured while reading the configuration file
                or the expected configparser.ConfigParser object=.
    """
    global USE_LOGFILE, LOG_VERBOSITY
    global TARGET_PATH, TARGETNAME_MAXLENGTH
    global SOURCE_PATH, SOURCENAME_MAXLENGTH
    global HASHID_MAXLENGTH, STRTAGS_MAXLENGTH

    parser = configparser.ConfigParser()

    try:
        parser.read(_configfile_name)
        USE_LOGFILE = parser["log file"]["use log file"] == "True"
        LOG_VERBOSITY = parser["log file"]["verbosity"]
        TARGET_PATH = ARGS.targetpath
        TARGETNAME_MAXLENGTH = int(parser["display"]["target filename.max length on console"])
        SOURCE_PATH = parser["source"]["path"]
        SOURCENAME_MAXLENGTH = int(parser["display"]["source filename.max length on console"])
        HASHID_MAXLENGTH = int(parser["display"]["hashid.max length on console"])
        STRTAGS_MAXLENGTH = int(parser["display"]["tag.max length on console"])
    except BaseException as exception:
        msg("  ! An error occured while reading " \
            "the config file \"{0}\".".format(_configfile_name))
        msg("  ! Python message : \"{0}\"".format(exception))
        return None

    return parser

#///////////////////////////////////////////////////////////////////////////////
def read_sieves():
    """
        read_sieves()
        ________________________________________________________________________

        Initialize SIEVES from the configuration file.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    SIEVES.clear()

    stop = False
    sieve_index = 1

    while not stop:
        if not PARAMETERS.has_section("source.sieve"+str(sieve_index)):
            stop = True
        else:
            SIEVES[sieve_index] = dict()

            if PARAMETERS.has_option("source.sieve"+str(sieve_index), "name"):
                SIEVES[sieve_index]["name"] = \
                                    re.compile(PARAMETERS["source.sieve"+str(sieve_index)]["name"])
            if PARAMETERS.has_option("source.sieve"+str(sieve_index), "size"):
                SIEVES[sieve_index]["size"] = PARAMETERS["source.sieve"+str(sieve_index)]["size"]
            if PARAMETERS.has_option("source.sieve"+str(sieve_index), "date"):
                SIEVES[sieve_index]["date"] = PARAMETERS["source.sieve"+str(sieve_index)]["date"]

        sieve_index += 1

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
    if not os.path.exists(normpath(DATABASE_FULLNAME)):
        msg("  = creating the database in the target path...")

        # let's create a new database in the target directory :
        db_connection = sqlite3.connect(DATABASE_FULLNAME)
        db_cursor = db_connection.cursor()

        if not ARGS.off:
            db_cursor.execute(SQL__CREATE_DB)

        db_connection.commit()
        db_connection.close()

        msg("  = ... database created.")

    db_connection = sqlite3.connect(DATABASE_FULLNAME)
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        TARGET_DB.append(db_record["hashid"])

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

    msg("  = informations about the \"{0}\" " \
        "(path: \"{1}\") source directory =".format(SOURCE_PATH,
                                                    normpath(SOURCE_PATH)))

    if not os.path.exists(normpath(SOURCE_PATH)):
        msg("    ! can't find source path \"{0}\" .".format(SOURCE_PATH))
        return
    if not os.path.isdir(normpath(SOURCE_PATH)):
        msg("    ! source path \"{0}\" isn't a directory .".format(SOURCE_PATH))
        return

    total_size = 0
    files_number = 0
    extensions = dict()  # (str)extension : [number of files, total size]
    for dirpath, _, fnames in os.walk(normpath(SOURCE_PATH)):
        for filename in fnames:
            fullname = os.path.join(normpath(dirpath), filename)
            size = os.stat(normpath(fullname)).st_size
            extension = os.path.splitext(normpath(filename))[1]

            if extension in extensions:
                extensions[extension][0] += 1
                extensions[extension][1] += size
            else:
                extensions[extension] = [1, size]

            total_size += size
            files_number += 1

    msg("    o files number : {0} file(s)".format(files_number))
    msg("    o total size : {0}".format(size_as_str(total_size)))
    msg("    o list of all extensions ({0} extension(s) found): ".format(len(extensions)))
    for extension in sorted(extensions):
        msg("      - {0:15} : {1} files, {2}".format(extension,
                                                     extensions[extension][0],
                                                     size_as_str(extensions[extension][1])))

    INFOS_ABOUT_SRC_PATH = (total_size, files_number, extensions)

#///////////////////////////////////////////////////////////////////////////////
def show_infos_about_target_path():
    """
        show_infos_about_target_path
        ________________________________________________________________________

        Display informations about the the target directory
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                (int) 0 if ok, -1 if an error occured
    """
    msg("  = informations about the \"{0}\" " \
        "(path: \"{1}\") target directory =".format(TARGET_PATH,
                                                    normpath(TARGET_PATH)))

    def draw_table(_rows, _data):
        """
                Draw a table with some <_rows> and fill it with _data.
        rows= ( ((str)row_name, (int)max length for this row), (str)separator)
        e.g. :
        rows= ( ("hashid", HASHID_MAXLENGTH, "|"), )

        _data : ( (str)row_content1, (str)row_content2, ...)
        """

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

    if not os.path.exists(normpath(TARGET_PATH)):
        msg("Can't find target path \"{0}\".".format(TARGET_PATH))
        return -1
    if not os.path.isdir(normpath(TARGET_PATH)):
        msg("target path \"{0}\" isn't a directory.".format(TARGET_PATH))
        return -1

    if not os.path.exists(os.path.join(normpath(TARGET_PATH),
                                       KATALSYS_SUBDIR, DATABASE_NAME)):
        msg("    o no database in the target directory o")
    else:
        db_connection = sqlite3.connect(DATABASE_FULLNAME)
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        # there's no easy way to know the size of a table in a database,
        # so we can't display the "empty database" warning before the following
        # code which reads the table.
        rows_data = []
        row_index = 0
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            sourcedate = \
                datetime.utcfromtimestamp(db_record["sourcedate"]).strftime(DATETIME_FORMAT)

            rows_data.append((db_record["hashid"],
                              db_record["name"],
                              db_record["strtags"],
                              db_record["sourcename"],
                              sourcedate))

            row_index += 1

        if row_index == 0:
            msg("    ! (empty database)")
        else:
            # beware : characters like "║" are forbidden (think to the cp1252 encoding
            # required by Windows terminal)
            draw_table(_rows=(("hashid/base64", HASHID_MAXLENGTH, "|"),
                              ("name", TARGETNAME_MAXLENGTH, "|"),
                              ("tags", STRTAGS_MAXLENGTH, "|"),
                              ("source name", SOURCENAME_MAXLENGTH, "|"),
                              ("source date", DATETIME_FORMAT_LENGTH, "|")),
                       _data=rows_data)

        db_connection.close()

    return 0

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
def show_hashid_of_a_file(filename):
    """
        show_hashid_of_a_file()
        ________________________________________________________________________

        The function gives the hashid of a file.
        ________________________________________________________________________

        PARAMETER
                o filename : (str) source filename

        no RETURNED VALUE
    """
    msg("  = hashid of \"{0}\" : \"{1}\"".format(filename,
                                                 hashfile64(filename)))

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
        return "0 byte"
    elif _size < 100000:
        return "{0} bytes".format(_size)
    elif _size < 1000000:
        return "~{0:.2f} Mo ({1} bytes)".format(_size/1000000.0,
                                                _size)
    else:
        return "~{0:.2f} Go ({1} bytes)".format(_size/1000000000.0,
                                                _size)

#///////////////////////////////////////////////////////////////////////////////
def normpath(_path):
    """
        normpath()
        ________________________________________________________________________

        Return a human-readable (e.g. "~" -> "/home/myhome/" on Linux systems),
        normalized version of a path.

        The returned string may be used as a parameter given to by
        os.path.exists() .
        ________________________________________________________________________

        PARAMETER : (str)_path

        RETURNED VALUE : the expected string
    """
    res = os.path.normpath(os.path.abspath(os.path.expanduser(_path)))

    if res == ".":
        res = os.getcwd()

    return res

#///////////////////////////////////////////////////////////////////////////////
def the_file_has_to_be_added(_filename, _size, _date):
    """
        the_file_has_to_be_added()
        ________________________________________________________________________

        Return True if a file (_filename, _size) can be choosed and added to
        the target directory, according to the sieves (stored in SIEVES).
        ________________________________________________________________________

        PARAMETERS
                o _filename     : (str) file's name
                o _size         : (int) file's size, in bytes.
                o _date         : (str) file's date

        RETURNED VALUE
                a boolean, giving the expected answer
    """
    evalstr = PARAMETERS["source"]["eval"]

    for sieve_index in SIEVES:
        sieve = SIEVES[sieve_index]

        evalstr = evalstr.replace("sieve"+str(sieve_index),
                                  str(eval_sieve_for_a_file(sieve, _filename, _size, _date)))

    try:
        # eval() IS a dangerous function : see the note about AUTHORIZED_EVALCHARS.
        for char in evalstr:
            if char not in AUTHORIZED_EVALCHARS:
                raise ProjectError("Error in configuration file : " \
                                   "trying to compute the \"{0}\" string; " \
                                   "wrong character '{1}'({2}) " \
                                   "used in the string to be evaluated. " \
                                   "Authorized " \
                                   "characters are {3}".format(evalstr,
                                                               char,
                                                               unicodedata.name(char),
                                                               "|"+"|".join(AUTHORIZED_EVALCHARS)))
        return eval(evalstr)
    except BaseException as exception:
        raise ProjectError("The eval formula in the config file " \
                           "contains an error. Python message : "+str(exception))

#///////////////////////////////////////////////////////////////////////////////
def the_file_has_to_be_added__date(_sieve, _date):
    """
        the_file_has_to_be_added__date()
        ________________________________________________________________________

        Function used by the_file_has_to_be_added() : check if the date of a
        file matches the sieve given as a parameter.
        ________________________________________________________________________

        PARAMETERS
                o _sieve        : a dict object; see documentation:selection
                o _date         : (str) file's datestamp (object datetime.datetime)

        RETURNED VALUE
                the expected boolean
    """
    # beware ! the order matters (<= before <, >= before >)
    if _sieve["date"].startswith("="):
        return _date == datetime.strptime(_sieve["date"][1:], DATETIME_FORMAT)
    elif _sieve["date"].startswith(">="):
        return _date >= datetime.strptime(_sieve["date"][2:], DATETIME_FORMAT)
    elif _sieve["date"].startswith(">"):
        return _date > datetime.strptime(_sieve["date"][1:], DATETIME_FORMAT)
    elif _sieve["date"].startswith("<="):
        return _date < datetime.strptime(_sieve["date"][2:], DATETIME_FORMAT)
    elif _sieve["date"].startswith("<"):
        return _date < datetime.strptime(_sieve["date"][1:], DATETIME_FORMAT)
    else:
        raise ProjectError("Can't analyse a 'date' field : "+_sieve["date"])

#///////////////////////////////////////////////////////////////////////////////
def the_file_has_to_be_added__name(_sieve, _filename):
    """
        the_file_has_to_be_added__name()
        ________________________________________________________________________

        Function used by the_file_has_to_be_added() : check if the name of a
        file matches the sieve given as a parameter.
        ________________________________________________________________________

        PARAMETERS
                o _sieve        : a dict object; see documentation:selection
                o _filename     : (str) file's name

        RETURNED VALUE
                the expected boolean
    """
    return re.match(_sieve["name"], _filename) is not None

#///////////////////////////////////////////////////////////////////////////////
def the_file_has_to_be_added__size(_sieve, _size):
    """
        the_file_has_to_be_added__size()
        ________________________________________________________________________

        Function used by the_file_has_to_be_added() : check if the size of a
        file matches the sieve given as a parameter.
        ________________________________________________________________________

        PARAMETERS
                o _sieve        : a dict object; see documentation:selection
                o _size         : (str) file's size

        RETURNED VALUE
                the expected boolean
    """
    res = False

    sieve_size = _sieve["size"] # a string like ">999" : see documentation:selection

    # beware !  the order matters (<= before <, >= before >)
    if sieve_size.startswith(">="):
        if _size >= int(sieve_size[2:]):
            res = True
    elif sieve_size.startswith(">"):
        if _size > int(sieve_size[1:]):
            res = True
    elif sieve_size.startswith("<="):
        if _size <= int(sieve_size[2:]):
            res = True
    elif sieve_size.startswith("<"):
        if _size < int(sieve_size[1:]):
            res = True
    elif sieve_size.startswith("="):
        if _size == int(sieve_size[1:]):
            res = True
    else:
        raise ProjectError("Can't analyse {0} in the sieve.".format(sieve_size))
    return res

#///////////////////////////////////////////////////////////////////////////////
def welcome():
    """
        welcome()
        ________________________________________________________________________

        Display a welcome message with some very broad informations about the
        program. This function may be called before reading the configuration
        file (confer the variable PARAMETERS).

        This function is called before the opening of the log file; hence, all
        the messages are only displayed on console (see welcome_in_logfile
        function)
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE

        sys.exit(-1) if the config file doesn't exist.
    """
    if ARGS.quiet:
        return

    strmsg = "=== {0} v.{1} " \
             "(launched at {2}) ===".format(__projectname__,
                                            __version__,
                                            TIMESTAMP_BEGIN.strftime("%Y-%m-%d %H:%M:%S"))
    msg("="*len(strmsg))
    msg(strmsg)
    msg("="*len(strmsg))

    # if the target file doesn't exist, it will be created later by main_warmup() :
    msg("  = target directory : \"{0}\" (path : \"{1}\")".format(ARGS.targetpath,
                                                                 normpath(ARGS.targetpath)))

    if ARGS.configfile is not None:
        msg("  = expected config file : \"{0}\" (path : \"{1}\")".format(ARGS.configfile,
                                                                         normpath(ARGS.configfile)))
    else:
        msg("  = no config file specified : let's search a config file in the current directory...")

    if ARGS.off:
        msg("  = --off option : no file will be modified, no directory will be created =")
        msg("  =                but the corresponding messages will be written in the  =")
        msg("  =                log file.                                              =")

#///////////////////////////////////////////////////////////////////////////////
def welcome_in_logfile():
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

        no PARAMETER, no RETURNED VALUE
    """
    msg(_msg="=== {0} v.{1} " \
        "(launched at {2}) ===".format(__projectname__,
                                       __version__,
                                       TIMESTAMP_BEGIN.strftime("%Y-%m-%d %H:%M:%S")),
        _for_logfile=True,
        _for_console=False)

    msg("  = using \"{0}\" as config file".format(ARGS.configfile),
        _for_logfile=True,
        _for_console=False)

#///////////////////////////////////////////////////////////////////////////////
#/////////////////////////////// STARTING POINT ////////////////////////////////
#///////////////////////////////////////////////////////////////////////////////
if __name__ == '__main__':
    main()
