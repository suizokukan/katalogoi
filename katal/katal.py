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
import logging
from logging.handlers import RotatingFileHandler
import operator
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
__version__ = "0.3.3"
__laststableversion__ = "0.3.3"  # when modifying this line, do not forget to launch fill_README.py
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

CONFIG = None # centralize all config (command line + configuration file)
              # see Config()

INFOS_ABOUT_SRC_PATH = (None, None, None)  # initialized by show_infos_about_source_path()
                                           # ((int)total_size, (int)files_number, (dict)extensions)

TARGET_DB = dict()      # see documentation:database; initialized by read_target_db()

SELECT = {}               # see documentation:selection; initialized by action__select()
SELECT_SIZE_IN_BYTES = 0  # initialized by action__select()
FILTER = None             # see documentation:selection; initialized by read_filters()

#===============================================================================
# loggers
#===============================================================================
def extra_logger(custom_parameters):
    """"
        extraLogger(custom_parameters)
        ________________________________________________________________________
        Mainly for syntax sugar.
        R
        It let to write logger.info(msg, color='blue') rather than
        logger.info(msg, extra={'color': 'blue'})
        ________________________________________________________________________
        PARAMETER
                o custom_parameters : (list) extra parameters added to a Logger
        RETURN
                A Logger class which can take custom_parameters as extra parameters
                and pass them to the extra argument of Logger

                Example:
                    extraLogger(['color']).info(msg, color='blue') is equivalent to
                    Logger.info(msg, extra={'color': 'blue'})
        """

    class CustomLogger(logging.Logger):
        """
            A custom Logger class
        """
        def _log(self, *args, **kwargs):
            extra = kwargs.get('extra', {})
            for parameter in custom_parameters:
                extra[parameter] = kwargs.get(parameter, None)
                kwargs.pop(parameter, None)
            kwargs['extra'] = extra

            return super()._log(*args, **kwargs)

    return CustomLogger

logging.setLoggerClass(extra_logger(['color']))

USE_LOGFILE = False     # (bool) initialized from the configuration file
LOGGER = logging.getLogger('katal')      # base logger, will log everywhere
FILE_LOGGER = logging.getLogger('file')  # will log only in file
LOGFILE_SIZE = 0                         # size of the current logfile.

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
CST__SQL__CREATE_DB = ('CREATE TABLE dbfiles ('
                       'hashid varchar(44) PRIMARY KEY UNIQUE, '
                       'partialhashid varchar(44), '
                       'size INTEGER, '
                       'name TEXT UNIQUE, '
                       'sourcename TEXT, sourcedate INTEGER, tagsstr TEXT)')

CST__TAG_SEPARATOR = ";"  # symbol used in the database between two tags.

CST__TASKS_SUBSUBDIR = "tasks"

CST__TRASH_SUBSUBDIR = "trash"

# 'Linux', 'Windows', 'Java' according to https://docs.python.org/3.5/library/platform.html
CST__PLATFORM = platform.system()

try:
    from xdg.BaseDirectory import load_first_config
except ImportError:
    CST__XDG_CONFIG = ''
else:
    CST__XDG_CONFIG = load_first_config(__projectname__)

################################################################################
class KatalError(Exception):
    """
        KatalError class

        A very basic class called when an error is raised by the program.
    """
    #///////////////////////////////////////////////////////////////////////////
    def __init__(self, value):
        Exception.__init__(self)
        self.value = value
    #///////////////////////////////////////////////////////////////////////////
    def __str__(self):
        return repr(self.value)

#///////////////////////////////////////////////////////////////////////////////

#///////////////////////////////////////////////////////////////////////////////
class ConfigError(configparser.Error):
    pass

#///////////////////////////////////////////////////////////////////////////////
class ColorFormatter(logging.Formatter):
    """
         A custom formatter class used to display color in stream output.

         see https://docs.python.org/3/library/logging.html .
    """
    # foreground colors :
    # (for more colors, see https://en.wikipedia.org/wiki/ANSI_escape_code)
    default = "\033[0m"
    red = "\033[0;31;1m"
    cyan = "\033[0;36;1m"
    white = "\033[0;37;1m"

    #///////////////////////////////////////////////////////////////////////////
    def format(self, record):
        """
                ColorFormatter.format()
                ________________________________________________________________

                see https://docs.python.org/3.5/library/logging.html :

                " The record’s attribute dictionary is used as the operand to a
                " string formatting operation. Returns the resulting string. [...]
                ________________________________________________________________

                PARAMETER :
                        o record : a logging.LogRecord object

                no RETURNED VALUE
        """
        color = record.color
        if CST__PLATFORM == 'Windows' or \
                not CFG_PARAMETERS.getboolean('log file', 'use color'):

            record.color_start = ''
            record.color_end = ''
        else:
            if color:
                record.color_start = getattr(self, color)
            else:
                if record.levelno <= logging.DEBUG:
                    record.color_start = ''
                    record.color_end = ''
                elif record.levelno <= logging.INFO:
                    record.color_start = self.default
                elif record.levelno <= logging.WARNING:
                    record.color_start = self.cyan
                else:
                    record.color_start = self.red

        record.color_end = self.default
        return super().format(record)


class Config(configparser.ConfigParser):
    def __init__(self):
        super().__init__(interpolation=None)

    def read_config(self, args=None):
        self.read_command_line_arguments(args)

        # TODO: download configfile
        self.read_dict(self.default_config())    # Initialize the defaults value
        self.read_all_config_files()
        self.read_dict(self.arguments_to_dict()) # Modifications from command line

        self.read_parameters_from_cfgfile()

    def arguments_to_dict(self):
        return {
            'display': {
                'verbosity': self.verbosity,
            },
            'source': {
                'strict comparison': self.strictcmp
            },
        }

    def check_args(self, parser):
        """
            check_args(self, parser)
            ________________________________________________________________________

            check the arguments of the command line. Raise a parser error if
            something is wrong.
            ________________________________________________________________________

            no PARAMETER, no RETURNED VALUE
        """
        # --select and --add can't be used simultaneously.
        # Already checked with the mutually exclusive group in the argparse
        # definition

        # --settagsstr must be used with --to :
        if self.settagsstr and not self.to:
            parser.error("please use --to in combination with --settagsstr")

        # --addtag must be used with --to :
        if self.addtag and not self.to:
            parser.error("please use --to in combination with --addtag")

        # --rmtags must be used with --to :
        if self.rmtags and not self.to:
            parser.error("please use --to in combination with --rmtags")

        # --strictcmp can only be used with --select or with --add :
        if self.strictcmp and not (self.add or self.select):
            parser.error("--strictcmp can only be used in combination with --select or with --add")

        # --copyto can only be used with --findtag :
        if self.copyto and not self.findtag:
            parser.error("--copyto can only be used in combination with --findtag .")

#///////////////////////////////////////////////////////////////////////////////
    def default_config(self):
        return {
        'source': {
            'path': '.',
            'eval': '*',
            'strict comparison': False,
        },
        'target': {
            'mode': 'copy',
            'name of the target file': '%i.%e',
        },
        'log file': {
            'use log file': True,
            'name': 'katal.log',
            'maximal size': 1e8,
        },
        'display': {
            'target filename.max length on console': 30,
            'source filename.max length on console': 40,
            'hashid.max length on console': 20,
            'tag.max length on console': 10,
            'verbosity': 'debug',
        },
        'actions': {
            'add': False,
            'cleandbrm': False
        },
        'tags': {}
    }

    def read_all_config_files(self):
        config_files = self.possible_paths_to_cfg()

        self.cfg_files = self.read(config_files)

        if self.configfile:
            try:
                with open(self.configfile) as f:
                    self.read_file(f)
                    self.cfg_files.append(self.configfile)
            except FileNotFoundError:
                print('  ! The config file "%s" (path : "%s") '
                    " doesn't exist. " % self.configfile, normpath(self.configfile))
                raise ConfigError

        if not self.cfg_files:
            print('  ! No config file has been found, ')
            print("    Use the -dlcfg/--downloaddefaultcfg option "
                  "to download a default config file.")
            raise ConfigError

    def read_command_line_arguments(self, args=None):
        """
            read_command_line_arguments(self)
            ________________________________________________________________________

            Read the command line arguments.
            Automatically check if arguments are correct ba calling self.check_args().
            In case of command line error, it is shown with parser.error(msg)
            ________________________________________________________________________

            no PARAMETER

            RETURNED VALUE
                    return self
        """
        parser = \
        argparse.ArgumentParser(description="{0} v. {1}".format(__projectname__, __version__),
                                epilog="{0} v. {1} ({2}), "
                                        "a project by {3} "
                                        "({4})".format(__projectname__,
                                                        __version__,
                                                        __license__,
                                                        __author__,
                                                        __email__),
                                formatter_class=argparse.ArgumentDefaultsHelpFormatter)

        exclusive_group = parser.add_mutually_exclusive_group()

        exclusive_group.add_argument('--add',
                            action="store_true",
                            help="# Select files according to what is described "
                                "in the configuration file "
                                "then add them to the target directory. "
                                "This option can't be used with the --select one."
                                "If you want more informations about the process, please "
                                "use this option in combination with --infos .")

        parser.add_argument('--addtag',
                            type=str,
                            help="# Add a tag to some file(s) in combination "
                                "with the --to option. ")

        parser.add_argument('-cfg', '--configfile',
                            type=str,
                            help="# Set the name of the config file, e.g. config.ini")

        parser.add_argument('--cleandbrm',
                            action="store_true",
                            help="# Remove from the database the missing files in the target path.")

        parser.add_argument('--copyto',
                            type=str,
                            help="# To be used with the --findtag parameter. Copy the found files "
                                "into an export directory.")

        parser.add_argument('-dlcfg', '--downloaddefaultcfg',
                            choices=("local", "home",),
                            help="# Download the default config file and overwrite the file having "
                                "the same name. This is done before the script reads the parameters "
                                "in the config file. Use 'local' to download in the current "
                                "directory, 'home' to download in the user's HOME directory.")

        parser.add_argument('--findtag',
                            type=str,
                            help="# Find the files in the target directory with the given tag. "
                                "The tag is a simple string, not a regex.")

        parser.add_argument('--infos',
                            action="store_true",
                            help="# Display informations about the source directory "
                                "given in the configuration file. Help the --select/--add "
                                "options to display more informations about the process : in "
                                "this case, the --infos will be executed before --select/--add")

        parser.add_argument('-n', '--new',
                            type=str,
                            help="# Create a new target directory")

        parser.add_argument('--off',
                            action="store_true",
                            help="# Don't write anything into the target directory or into "
                                "the database, except into the current log file. "
                                "Use this option to simulate an operation : you get the messages "
                                "but no file is modified on disk, no directory is created.")

        parser.add_argument('--rebase',
                            type=str,
                            help="# Copy the current target directory into a new one : you "
                                "rename the files in the target directory and in the database. "
                                "First, use the --new option to create a new target directory, "
                                "modify the .ini file of the new target directory "
                                "(modify [target]name of the target files), "
                                "then use --rebase with the name of the new target directory")

        parser.add_argument('--reset',
                            action="store_true",
                            help="# Delete the database and the files in the target directory")

        parser.add_argument('--rmnotags',
                            action="store_true",
                            help="# Remove all files without a tag")

        parser.add_argument('--rmtags',
                            action="store_true",
                            help="# Remove all the tags of some file(s) in combination "
                                "with the --to option. ")

        exclusive_group.add_argument('-s', '--select',
                            action="store_true",
                            help="# Select files according to what is described "
                                "in the configuration file "
                                "without adding them to the target directory. "
                                "This option can't be used with the --add one."
                                "If you want more informations about the process, please "
                                "use this option in combination with --infos .")

        parser.add_argument('--settagsstr',
                            type=str,
                            help="# Give the tag to some file(s) in combination "
                                "with the --to option. "
                                "Overwrite the ancient tag string. "
                                "If you want to empty the tags' string, please use a space, "
                                "not an empty string : otherwise the parameter given "
                                "to the script wouldn't be taken in account by the shell")

        parser.add_argument('-si', '--sourceinfos',
                            action="store_true",
                            help="# Display informations about the source directory")

        parser.add_argument('--strictcmp',
                            action="store_true",
                            help="# To be used with --add or --select. Force a bit-to-bit comparision"
                                "between files whose hashid-s is equal.")

        parser.add_argument('--targetpath',
                            type=str,
                            default=".",
                            help="# Target path, usually '.' . If you set path to . (=dot character)"
                                ", it means that the source path is the current directory"
                                " (=the directory where the script katal.py has been launched)")

        parser.add_argument('-ti', '--targetinfos',
                            action="store_true",
                            help="# Display informations about the target directory")

        parser.add_argument('-tk', '--targetkill',
                            type=str,
                            help="# Kill (=move to the trash directory) one file from "
                                "the target directory."
                                "DO NOT GIVE A PATH, just the file's name, "
                                "without the path to the target directory")

        parser.add_argument('--to',
                            type=str,
                            help="# Give the name of the file(s) concerned by --settagsstr. "
                            "wildcards accepted; e.g. to select all .py files, use '*.py' . "
                            "Please DON'T ADD the path to the target directory, only the filenames")

        parser.add_argument('--usentfsprefix',
                            action="store_true",
                            help="# Force the script to prefix filenames by a special string "
                                "required by the NTFS for long filenames, namely \\\\?\\")

        parser.add_argument('--verbosity',
                            choices=("none", "normal", "high"),
                            default='normal',
                            help="# Console verbosity : "
                                "'none'=no output to the console, no question asked on the console; "
                                "'normal'=messages to the console "
                                "and questions asked on the console; "
                                "'high'=display discarded files. A question may be asked only by "
                                "using the following arguments : "
                                "--new, --rebase, --reset and --select")

        parser.add_argument('--version',
                            action='version',
                            version="{0} v. {1}".format(__projectname__, __version__),
                            help="# Show the version and exit")

        parser.add_argument('--whatabout',
                            type=str,
                            help="# Say if the file[the files in a directory] already in the "
                                "given as a parameter is in the target directory "
                                "notwithstanding its name.")

        parser.parse_args(args=args, namespace=self)

        self.check_args(parser)

        return self

    #///////////////////////////////////////////////////////////////////////////////
    def possible_paths_to_cfg(self):
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

        res.append(os.path.join(normpath("~"), ".katal"))
        if CST__XDG_CONFIG:
            res.append(CST__XDG_CONFIG)

        if CST__PLATFORM == 'Windows':
            res.append(os.path.join(normpath("~"),
                                    "Local Settings",
                                    "Application Data",
                                    "katal"))

        res.append(os.path.join(normpath(ARGS.targetpath),
                                CST__KATALSYS_SUBDIR))
        res.append(normpath(ARGS.targetpath))

        cfg_localisation = [os.path.join(cfg_path, CST__DEFAULT_CONFIGFILE_NAME)
                            for cfg_path in res]

        return cfg_localisation

    #///////////////////////////////////////////////////////////////////////////////
    def read_parameters_from_cfgfile(self):
        """
            read_parameters_from_cfgfile()
            ________________________________________________________________________

            Read the configfile and return the parser. If an error occured, a
            ConfigError is raised.

            If the mode is set to 'nocopy', parser["target"]["name of the target files"]
            is set to "%i" .
            ________________________________________________________________________

            NO PARAMETER

            RETURNED VALUE
                    self
            EXCEPTION
                    A ConfigError if an error occured while reading the configuration file

        """
        global USE_LOGFILE

        parser = self
        try:
            USE_LOGFILE = parser["log file"].getboolean("use log file")
            # just to check the existence of the following values in the configuration file :
            parser["log file"]["maximal size"]
            parser["log file"]["name"]
            parser["target"]["name of the target files"]
            parser["target"]["mode"]
            parser["source"]["eval"]
            parser["display"]["target filename.max length on console"]
            parser["display"]["hashid.max length on console"]
            parser["display"]["tag.max length on console"]
            parser["display"]["source filename.max length on console"]
            parser["source"]["path"]
        except KeyError as exception:
            print("  ! An error occured while reading config files.")
            print('  ! Your configuration file lacks a specific value : "%s".' % exception)
            print("  ... you should download a new default config file : "
                        "see -dlcfg/--downloaddefaultcfg option")
            raise ConfigError
        except configparser.Error as exception:
            print("  ! An error occured while reading the config files.")
            print(exception)
            raise ConfigError

        if parser["target"]["mode"] == 'nocopy':
            parser["target"]["name of the target files"] = "%i"

            print('  *  since "mode"=="nocopy", the value of "[target]name of the target files" ')
            print("     is neutralized and set to '%i' (i.e. the database index : '1', '2', ...)")

        return parser


class Filter:
    """
    Filter class. Filter files according to conditions in config file
    ________________________________________________________________________

    PARAMETERS
            o config :  (Configparser section, default=None) the config section
                        where is defined the filter. If provided, the filter
                        will analyze to find conditions, else nothing is done.
            o name   :  (str, default='') the name of the parser, used for
                        formatting.

    ATTRIBUTES
            o self.conditions : (dict) A dict of conditions a file must succeed.
                        The key is the name of condition, used for formatting,
                        and the values are funtion that take the name of the
                        file as parameter and return True if the file suceed the
                        conditions
            o self.name : the name of the Filter, from the name parameter.
    """
    def __init__(self, config=None, name=''):
        self.conditions = {}
        self.name = name
        if config is not None:
            self.read_config(config)

    def read_config(self, config):
        """
        self.read_config(config) Extract conditions from config section
        ________________________________________________________________________

        Analyze the ConfigParser section corresponding to the filter, and extract
        the different conditions a file must check.
        Populate self.conditions.
        ________________________________________________________________________

        PARAMETERS
                o config :  (Configparser) the config section to analyze.

        no RETURNED VALUE
        """

        if 'name' and 'iname' in config:
            LOGGER.warning("  ! Filter %s has two conditions about name: 'name'"
                           " and 'iname'.\n"
                           "    By default, use only the iname condition",
                           config.name)

        # Use first iname if defined, else name
        if 'iname' in config:
            regex = re.compile(config['iname'], re.IGNORECASE)
        elif 'name' in config:
            regex = re.compile(config['name'])
        else:
            regex = None

        self.conditions['name'] = self.match_regex(regex)
        self.conditions['size'] = self.match_size(config.get('size'))
        self.conditions['date'] = self.match_date(config.get('date'))
        self.conditions['name not existing'] = \
            self.match_name_not_existing(config.get('name not existing'))

    def match_date(self, filter_date):
        """
        self.match_date(filter_date) -> function
        ________________________________________________________________________

        Analyze the parameter filter_date and return a function which test the
        file against the date.
        ________________________________________________________________________

        PARAMETERS
                o filter_date : (str) the string from config file corresponding
                                to the condition on date (eg. >2016-09).

        RETURNED VALUE
                o function(file_name) : function which test if the file succeed
                                        to the date condition.
                                        If filter_date is evaluated to False,
                                        always return True
        """
        if not filter_date:
            return lambda name: True

        # beware !  the order matters (<= before <, >= before >)
        for condition, op in (('>=', operator.ge),
                              ('>',  operator.gt),
                              ('<=', operator.le),
                              ('<' , operator.lt),
                              ('=' , operator.eq)):
            if filter_date.startswith(condition):
                filter_date = filter_date[(len(condition)):]
                break
        else:
            raise KatalError("Can't analyse a 'date' field : " + filter_date)

        # Parse the filter date
        for time_format in ('%Y-%m-%d %H:%M',   # '2015-09-17 20:01'
                            '%Y-%m-%d',         # '2015-09-17
                            '%Y-%m',            # '2015-09'
                            '%Y',               # '2015'
                            ):

            try:
                date = datetime.strptime(filter_date, time_format)
            except ValueError:
                pass
            else:
                break
        else:
            raise KatalError("Can't analyse the 'date' field {}, see "
                             "configuration example for correct format".format(filter_date))


        def return_match(name):
            # ..................................................................
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link on the
            #   "size = os.stat(normpath(fullname)).st_size" line (see below).
            # ..................................................................
            if not os.path.exists(name):
                return False

            # do not use utcfromtimestamp ; since time_format is given in local
            # tz, time must be also in local tz.
            time = datetime.fromtimestamp(os.stat(name).st_mtime)
            time = time.replace(second=0, microsecond=0)
            return op(time, filter_date)

        return return_match

    def match_regex(self, regex):
        """
        self.match_regex(regex) -> test_function
        ________________________________________________________________________

        Analyze the parameter filter_regex and return a function which test if
        the basename of the file match the regex
        ________________________________________________________________________

        PARAMETERS
                o regex : (str) the string from config file corresponding
                                to the condition on date (eg. .*\.jpg).

        RETURNED VALUE
                o function(file_name) : function which test if the file match the regex
                                        If regex is evaluated to False,
                                        always return True
        """
        if not regex:
            return lambda name: True

        def return_match(name):
            # TODO: search or match ? Search will let to write for ex. .jpg instead
            # of *.jpg since it doesn't match from the start of the string, but it
            # may have side effects.
            return regex.match(os.path.basename(name)) is not None

        return return_match

    def match_size(self, filter_size):
        """
        self.match_file(filter_size) -> test_function
        ________________________________________________________________________

        Analyze the parameter filter_regex and return a function which test if
        the basename of the file match the regex
        ________________________________________________________________________

        PARAMETERS
                o filter_size: (str) the string from config file corresponding
                                to the condition on size (eg. >1MB).

        RETURNED VALUE
                o function(file_name) : function which test if the file succeed
                                        the condition on size
                                        If filter_size is evaluated to False,
                                        always return True
        """
        if not filter_size:
            return lambda name: True

        # Parse filter definition

        # remove possible space inside definition
        filter_size = filter_size.replace(' ', '')

        # beware !  the order matters (<= before <, >= before >)
        for condition, op in (('>=', operator.ge),
                              ('>',  operator.gt),
                              ('<=', operator.le),
                              ('<' , operator.lt),
                              ('=' , operator.eq)):
            if filter_size.startswith(condition):
                filter_size = filter_size[(len(condition)):]
                break
        else:
            raise KatalError("Can't analyse {0} in the filter.".format(filter_size))

        multiple = 1
        for suffix, _multiple in CST__MULTIPLES:
            if filter_size.endswith(suffix):
                multiple = _multiple
                filter_size = filter_size[:-len(suffix)]
                break
        else:
            if not filter_size[-1].isdigit():
                raise KatalError("Can't analyse {0} in the filter. "
                                "Available multiples are : {1}".format(filter_size,
                                                                        CST__MULTIPLES))
        try:
            match_size = float(filter_size) * multiple
        except ValueError:
            raise KatalError("Can't analyse {0} in the filter. "
                             "Format must be for example size : >= 10 MB".format(filter_size))

        def return_match(name):
            # ..................................................................
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link
            # ..................................................................
            if not os.path.exists(name):
                return False

            size = os.stat(name).st_size
            return op(size, match_size)

        return return_match

    def match_operator(self, op, filter2=None):
        """
        self.match_operator(op, filter2=None) -> test_function
        ________________________________________________________________________

        Test the boolean operation between self and filter2.
        For example, self.match_operator(operator.and_, filter2)(file)
            -> self(file) and filter2(file)
        ________________________________________________________________________

        PARAMETERS
                o op : the boolean operation to make between filters (eg. operator.and)
                o filter2: (Filter default=None) the second filter to do the operation

        RETURNED VALUE
                o function(file_name) : function which test if the file succeed
                                        the condition on operations of Filters.
                                        If op is evaluated to False,
                                        always return True
        """
        if not op:
            return lambda name: True

        def return_match(name):
            if filter2 is None:             # Negation is not a binary operator
                return op(self(name))
            else:
                return op(self(name), filter2(name))

        return return_match

    def match_name_not_existing(self, name_template=None):
        """
        self.match_name_not_existing(name_template) -> test_function
        ________________________________________________________________________

        Analyze the name_template and return a function which test if the
        name_template modified accoding the file is already in the db.
        ________________________________________________________________________

        PARAMETERS
                o filter_name_not_existing: (str) the string from config file
                corresponding to the name_template to test

        RETURNED VALUE
                o function(file_name) : function which test if the file succeed
                the condition
                If filter_size is evaluated to False, always return True
        """
        if not name_template:
            return lambda name: True

        list_names = set(name for _, _, name in TARGET_DB.items())

        def return_match(name):
            res = name
            size = os.stat(name).st_size
            time = datetime.fromtimestamp(os.stat(name).st_mtime)
            time = time.replace(second=0, microsecond=0)

            basename, ext = get_filename_and_extension(os.path.basename(name))

            # beware : order matters !
            res = res.replace("%ht", hex(time.timestamp())[2:])
            res = res.replace("%h", hashfile64(name))

            res = res.replace("%ff", remove_illegal_characters(basename))
            res = res.replace("%f", basename)

            res = res.replace("%pp", remove_illegal_characters(os.path.dirname(name)))
            res = res.replace("%p", os.path.dirname(name))

            res = res.replace("%ee", remove_illegal_characters(ext))
            res = res.replace("%e", ext)

            res = res.replace("%s", str(size))

            res = res.replace("%dd", remove_illegal_characters(
                time.strftime(CST__DTIME_FORMAT)))

            res = res.replace("%t", str(time.timestamp))

            if '%i' in res:
                raise KatalError('"%i" not allowed in "name not already existing"'
                                 ' config key')

            res = res.replace("%i",
                            remove_illegal_characters(str(database_index)))

            return res not in list_names

    def test(self, file_name):
        """
        self.test(file_name) -> check if the file succed to all conditions"
        ________________________________________________________________________

        PARAMETERS
                o file_name : the full name of the file to test

        RETURNED VALUE:
                o True if file succed to all conditions, else False
        """
        list_tests_failled = [key for key, test in self.conditions.items()
                              if not test(file_name)]

        if list_tests_failled:
            LOGGER.info('  o The following tests failed for filter "{}" and file "{}": '
                        '{}'.format(self.name, file_name, list_tests_failled))
            return False
        else:
            return True

    def __call__(self, file_name):
        """
        self(file_name) -> self.test(file_name)
        """
        return self.test(file_name)

    def __and__(self, filter2):
        """
        Return (self & filter2)

        (self & filter2)(file_name) <=> self(file_name) and filter2(file_name)
        """
        f = Filter()
        f.conditions['and'] = self.match_operator(operator.and_, filter2)
        return f

    def __or__(self, filter2):
        """
        Return (self | filter2)

        (self | filter2)(file_name) <=> self(file_name) or² filter2(file_name)
        """
        f = Filter()
        f.conditions['or'] = self.match_operator(operator.or_, filter2)
        return f

    def __xor__(self, filter2):
        """
        Return (self ^ filter2)

        (self ^ filter2)(file_name) <=> self(file_name) xor filter2(file_name)
        """
        f = Filter()
        f.conditions['xor'] = self.match_operator(operator.xor, filter2)
        return f

    def __invert__(self):
        """
        Return ~self (not self)

        (~ self)(file_name) <=> not self(file_name)
        """
        f = Filter()
        f.conditions['not'] = self.match_operator(operator.not_)
        return f

#///////////////////////////////////////////////////////////////////////////////


class SelectElement:
    def __init__(self, fullname):
        global SELECT_SIZE_IN_BYTES

        self.fullname = normpath(fullname)
        self.path, filename = os.path.split(self.fullname)
        self.filename_no_extens, self.extension = get_filename_and_extension(filename) #TODO Put get_filename... as e method ?
        self.dirpath = os.path.dirname(fullname)
        self.size = os.stat(fullname).st_size
        self.time = os.stat(fullname).st_mtime
        # TODO: storing th etimestampl may be more practical
        self.date = datetime.fromtimestamp(self.time).strftime(CST__DTIME_FORMAT)
        self.database_index = len(TARGET_DB) + len(SELECT) # TODO: ensure this is correct

        self.partialhashid = hashfile64(filename=self.fullname,
                                        stop_after=CST__PARTIALHASHID_BYTESNBR),
        self.hashid = hashfile64(filename=self.fullname)

        self.targetname = self.create_target_name()
        self.targettags = self.create_target_tags()

        SELECT_SIZE_IN_BYTES += self.size

    def create_target_name(self):
        """
            create_target_name()
            ________________________________________________________________________

            Create the name of a file (a target file) from various informations
            given by the parameters. The function reads the string stored in
            parameters["target"]["name of the target files"] and replaces some
            keywords in the string by the parameters given to this function.

            see the available keywords in the documentation.
                (see documentation:configuration file)

            caveat : in the .ini files, '%' have to be written twice (as in
                    '%%p', e.g.) but Python reads it as if only one % was
                    written.
            ________________________________________________________________________

            PARAMETERS
                    o parameters                   : an object returned by
                                                    read_parameters_from_cfgfile(),
                                                    like CFG_PARAMETERS
                    o hashid                       : (str)
                    o filename_no_extens           : (str)
                    o path                         : (str
                    o extension                    : (str)
                    o _size                        : (int)
                    o date                         : (str) see CST__DTIME_FORMAT
                    o database_index               : (int)

            About the underscore before "_size" :
            confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
            " If a function argument's name clashes with a reserved keyword, it is generally
            " better to append a single trailing underscore rather than use an abbreviation
            " or spelling corruption.

            RETURNED VALUE
                    (str)name
        """
        return self.add_keywords_in_targetstr(parameters["target"]["name of the target files"])

    #/////////////////////////////////////////////////////////////////////////////////////////
    def create_target_tags(self):
        """
            create_target_tags()
            ________________________________________________________________________

            Create the tags of a file (a target file) from various informations
            given by the parameters. The function reads the string stored in
            parameters["target"]["tags"] and replaces some
            keywords in the string by the parameters given to this function.

            see the available keywords in the documentation.
                (see documentation:configuration file)

            caveat : in the .ini files, '%' have to be written twice (as in
                    '%%p', e.g.) but Python reads it as if only one % was
                    written.
            ________________________________________________________________________

            PARAMETERS
                    o parameters                   : an object returned by
                                                    read_parameters_from_cfgfile(),
                                                    like CFG_PARAMETERS
                    o hashid                       : (str)
                    o filename_no_extens           : (str)
                    o path                         : (str
                    o extension                    : (str)
                    o _size                        : (int)
                    o date                         : (str) see CST__DTIME_FORMAT
                    o database_index               : (int)

            About the underscore before "_size" :
            confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
            " If a function argument's name clashes with a reserved keyword, it is generally
            " better to append a single trailing underscore rather than use an abbreviation
            " or spelling corruption.

            RETURNED VALUE
                    (str)name
        """
        return self.add_keywords_in_targetstr(srcstring=parameters["target"]["tags"])

    def __eq__(self, other):
        if self.hashid != other.hashid:
            return False
        elif self.partialhashid != other.partialhashid:
            return False
        else:
            # We have to do a bit-to-bit comparison
            return filecmp.cmp(element.filename, TARGET_DB[hashid][2], shallow=False)

    def __hash__(self):
        return hash(hashid)

    #///////////////////////////////////////////////////////////////////////////////
    def __set__(self, value):
        """
        setattr(self, value)
        __________________________________________________________________________

        The object should be immutable, so that its hash doesn't change. So this
        function should prevent any attribute change.
        However, this is not a very strong protection, but it should prevent most
        of changes
        """
        raise TypeError("Can't set attributes of 'SelectElement' type")

    def add_keywords_in_targetstr(self, srcstring):
        """
            add_keywords_in_targetstr()
            ________________________________________________________________________

            The function replaces some keywords in the string by the parameters given
            to this function.
            The function returned a string which may be used to create target files.

            see the available keywords in the documentation.
                (see documentation:configuration file)
            ________________________________________________________________________

            PARAMETERS
                    o srcstring                    : (str)
                    o hashid                       : (str)
                    o filename_no_extens           : (str)
                    o path                         : (str
                    o extensiont : in the .ini files, '%' have to be written twice (as in
                                    '%%p', e.g.) but Python reads it as if only one % was
                                                    written.
                                                    : (str)
                    o _size                        : (int)
                    o date                         : (str) see CST__DTIME_FORMAT
                    o database_index               : (int)

            About the underscore before "_size" :
            confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
            " If a function argument's name clashes with a reserved keyword, it is generally
            " better to append a single trailing underscore rather than use an abbreviation
            " or spelling corruption.

            RETURNED VALUE
                    (str)the expected string
        """
        res = srcstring

        # beware : order matters !
        res = res.replace("%ht", hex(int(self.time))[2:])

        res = res.replace("%h", self.hashid)

        res = res.replace("%ff", remove_illegal_characters(self.filename_no_extens))
        res = res.replace("%f", self.filename_no_extens)

        res = res.replace("%pp", remove_illegal_characters(self.path))
        res = res.replace("%p", self.path)

        res = res.replace("%ee", remove_illegal_characters(self.extension))
        res = res.replace("%e", self.extension)

        res = res.replace("%s", str(self.size))

        res = res.replace("%dd", remove_illegal_characters(self.date))

        res = res.replace("%t", str(int(self.time)))

        res = res.replace("%i", str(self.database_index))

        return res

    #///////////////////////////////////////////////////////////////////////////////


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
    LOGGER.info("  = copying data =")

    db_connection = sqlite3.connect(get_database_fullname())
    db_cursor = db_connection.cursor()

    if get_disk_free_space(ARGS.targetpath) < SELECT_SIZE_IN_BYTES*CST__FREESPACE_MARGIN:
        LOGGER.warning("    ! Not enough space on disk. Stopping the program.")
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
                LOGGER.info("    ... (%s/%s) due to the nocopy mode argument, "
                            "\"%s\" will be simply added "
                            "in the target database.", index+1, len_select,
                            complete_source_filename)

            elif CFG_PARAMETERS["target"]["mode"] == "copy":
                # copying the file :
                LOGGER.info("    ... (%s/%s) about to " "copy \"%s\" to \"%s\" .",
                            index+1, len_select, complete_source_filename, target_name)
                shutil.copyfile(complete_source_filename, target_name)
                os.utime(target_name, (sourcedate, sourcedate))

            elif CFG_PARAMETERS["target"]["mode"] == "move":
                # moving the file :
                LOGGER.info("    ... (%s/%s) about to " "move \"%s\" to \"%s\" .",
                            index+1, len_select, complete_source_filename, target_name)
                shutil.move(complete_source_filename, target_name)
                os.utime(target_name, (sourcedate, sourcedate))

        files_to_be_added.append((hashid,
                                  SELECT[hashid].partialhashid,
                                  SELECT[hashid].size,
                                  SELECT[hashid].targetname,
                                  complete_source_filename,
                                  sourcedate,
                                  SELECT[hashid].targettags))

    LOGGER.info("    = all files have been copied, let's update the database...")

    try:
        if not ARGS.off:
            db_cursor.executemany('INSERT INTO dbfiles VALUES (?,?,?,?,?,?,?)', files_to_be_added)

    except sqlite3.IntegrityError as exception:
        LOGGER.error("!!! An error occured while writing the database : %s\n"
                     "!!! files to be added", str(exception))
        for file_to_be_added in files_to_be_added:
            LOGGER.error("     ! hashid=%s; partialhashid=%s; size=%s; name=%s; sourcename=%s; "
                         "sourcedate=%s; tagsstr=%s", *file_to_be_added)
        raise KatalError("An error occured while writing the database : "+str(exception))

    db_connection.commit()
    db_connection.close()

    LOGGER.info("    = ... database updated.")

    # returned value : 0 = success
    return 0

#///////////////////////////////////////////////////////////////////////////////
def action__addtag(tag, dest):
    """
        action__addtag()
        ________________________________________________________________________

        Add a tag dest the files given by the "dest" parameter.
        ________________________________________________________________________

        PARAMETERS
                o tag          : (str) new tag to be added
                o dest         : (str) a regex string describing what files are
                                 concerned
    """
    LOGGER.info("  = let's add the tag string \"%s\" to %s", tag, dest)
    modify_the_tag_of_some_files(tag=tag, dest=dest, mode="append")

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
    LOGGER.info("  = clean the database : remove missing files from the target directory.")

    if not os.path.exists(normpath(get_database_fullname())):
        LOGGER.warning("    ! no database found.")
        return

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    files_to_be_rmved_from_the_db = []  # hashid of the files
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        if not os.path.exists(os.path.join(normpath(ARGS.targetpath), db_record["name"])):
            files_to_be_rmved_from_the_db.append(db_record["hashid"])
            LOGGER.info("    o about to remove \"%s\" "
                        "from the database", os.path.join(normpath(ARGS.targetpath),
                                                          db_record["name"]))

    if len(files_to_be_rmved_from_the_db) == 0:
        LOGGER.info("    * no file to be removed : the database is ok.")
    else:
        for hashid in files_to_be_rmved_from_the_db:
            if not ARGS.off:
                LOGGER.info("    o removing \"%s\" record "
                            "from the database", hashid)
                db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))
                db_connection.commit()

    db_connection.close()
    if not ARGS.off:
        LOGGER.info("    o ... done : removed %s "
                    "file(s) from the database", len(files_to_be_rmved_from_the_db))

#///////////////////////////////////////////////////////////////////////////////
def action__downloadefaultcfg(targetname=CST__DEFAULT_CONFIGFILE_NAME, location="local"):
    """
        action__downloadefaultcfg()
        ________________________________________________________________________

        Download the default configuration file; save it in the current directory
        (location='local') or in the user's HOME directory (location='home').

        No log messages for this function, everything is printed to the console.
        ________________________________________________________________________

        PARAMETERS :
            o (str) targetname : the new name of the downloaded file
            o (str) location : "local" or "home"

        RETURNED VALUE :
            (bool) success
    """
    print("  = downloading the default configuration file...")
    print("    ... trying to download %s from %s", targetname, CST__DEFAULTCFGFILE_URL)

    try:
        if not ARGS.off:
            with urllib.request.urlopen(CST__DEFAULTCFGFILE_URL) as response, \
                 open(targetname, 'wb') as out_file:
                shutil.copyfileobj(response, out_file)
        print("  * download completed : \"{0}\" (path : \"{1}\")".format(targetname,
                                                                         normpath(targetname)))

        if location == 'home':
            newname = os.path.join(possible_paths_to_cfg()[-1],
                                   os.path.basename(targetname))
            print("  * Since you wrote '--downloaddefaultcfg=home', "
                  "let's move the download file to the user's home directory...")
            print("    namely {0} -> {1}".format(targetname, newname))
            shutil.move(targetname, newname)

        return True

    except urllib.error.URLError as exception:
        print("  ! An error occured : {0}\n"
              "  ... if you can't download the default config file, what about simply\n"
              "  ... copy another config file to the target directory ?\n"
              "  ... In a target directory, the config file is \n"
              "in the \"{1}\" directory.".format(exception,
                                                 os.path.join(CST__KATALSYS_SUBDIR)))
        return False

#///////////////////////////////////////////////////////////////////////////////
def action__findtag(tag):
    """
        action__findtag()
        ________________________________________________________________________

        Display the files tagged with a tag. "tag" is a simple string, not a
        regex. The function searches a substring "tag" in the tags' string.

        With --copyto, copy the selected files into the directory whose name
        is given by ARGS.copyto .
        ________________________________________________________________________

        PARAMETER
            o tag : (str)the searched tag

        no RETURNED VALUE
    """
    LOGGER.info("  = searching the files with the tag \"%s\"", tag)

    if not os.path.exists(normpath(get_database_fullname())):
        LOGGER.warning("    ! no database found.")
        return

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    res = []
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        if tag in db_record["tagsstr"]:

            res.append(db_record["name"])
            LOGGER.info("    o \"%s\" : \"%s\"",
                        db_record["name"], tagsstr_repr(db_record["tagsstr"]))

    len_res = len(res)
    if len_res == 0:
        LOGGER.info("    o no file matches the tag \"%s\" .", tag)
    elif len_res == 1:
        LOGGER.info("    o one file matches the tag \"%s\" .", tag)
    else:
        LOGGER.info("    o %s files match the tag \"%s\" .", len_res, tag)

    db_connection.commit()
    db_connection.close()

    # --copyto argument :
    if ARGS.copyto:
        LOGGER.info("    o copying the files into \"%s\" (path: \"%s\")",
                    ARGS.copyto, normpath(ARGS.copyto))

        if not os.path.exists(normpath(ARGS.copyto)):
            LOGGER.info("    * let's create \"%s\" (path: \"%s\"",
                        ARGS.copyto, normpath(ARGS.copyto))
            if not ARGS.off:
                os.mkdir(normpath(ARGS.copyto))

        for i, filename in enumerate(res):
            src = os.path.join(normpath(ARGS.targetpath), filename)
            dest = os.path.join(normpath(ARGS.copyto), filename)
            LOGGER.info("    o (%s/%s) copying \"%s\" as \"%s\"...",
                        i+1, len_res, src, dest)
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
    LOGGER.info("  = informations =", color="white")
    show_infos_about_source_path()
    return show_infos_about_target_path()

#///////////////////////////////////////////////////////////////////////////////
def action__new(targetname):
    """
        action__new()
        ________________________________________________________________________

        Create a new target directory.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    LOGGER.warning("  = about to create a new target directory "
                   "named \"%s\" (path : \"%s\")", targetname, normpath(targetname))

    if os.path.exists(normpath(targetname)):
        LOGGER.warning("  ! can't go further : the directory already exists.")
        return

    if not ARGS.off:
        LOGGER.warning("  ... creating the target directory with its sub-directories...")
        os.mkdir(normpath(targetname))
        os.mkdir(os.path.join(normpath(targetname), CST__KATALSYS_SUBDIR))
        os.mkdir(os.path.join(normpath(targetname), CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR))
        os.mkdir(os.path.join(normpath(targetname), CST__KATALSYS_SUBDIR, CST__TASKS_SUBSUBDIR))
        os.mkdir(os.path.join(normpath(targetname), CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR))

        create_empty_db(os.path.join(normpath(targetname),
                                     CST__KATALSYS_SUBDIR,
                                     CST__DATABASE_NAME))

    if ARGS.verbosity != 'none':
        answer = \
            input(("\nDo you want to download the default config file "
                   "into the expected directory ? (y/N) "))

        if answer in ("y", "yes"):
            res = action__downloadefaultcfg(targetname=os.path.join(normpath(targetname),
                                                                    CST__KATALSYS_SUBDIR,
                                                                    CST__DEFAULT_CONFIGFILE_NAME),
                                            location="local")
            if not res:
                LOGGER.warning("  ! A problem occured : "
                               "the creation of the target directory has been aborted.")

    LOGGER.warning("  ... done with the creation of \"%s\" as a new target directory.", targetname)

#///////////////////////////////////////////////////////////////////////////////
def action__rebase(newtargetpath):
    """
        action__rebase()
        ________________________________________________________________________

        Copy the current target directory into a new one, modifying the filenames.
        ________________________________________________________________________

        PARAMETER :
                o newtargetpath        : (str) path to the new target directory.

        no RETURNED VALUE
    """
    source_path = CFG_PARAMETERS["source"]["path"]

    LOGGER.info("  = copying the current target directory into a new one.")
    LOGGER.info("    o from %s (path : \"%s\")", source_path, normpath(source_path))

    LOGGER.info("    o to   %s (path : \"%s\")", newtargetpath, normpath(newtargetpath))

    to_configfile = os.path.join(newtargetpath,
                                 CST__KATALSYS_SUBDIR,
                                 CST__DEFAULT_CONFIGFILE_NAME)
    LOGGER.info("    o trying to read dest config file %s "
                "(path : \"%s\") .", to_configfile, normpath(to_configfile))

    dest_params = read_parameters_from_cfgfile(normpath(to_configfile))

    if dest_params is None:
        LOGGER.warning("    ! can't read the dest config file !")
        return

    LOGGER.info("    o config file found and read (ok)")
    LOGGER.info("    o new filenames' format : %s",
                dest_params["target"]["name of the target files"])
    LOGGER.info("    o tags to be added : %s",
                dest_params["target"]["tags"])

    new_db = os.path.join(normpath(newtargetpath), CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)
    if not ARGS.off:
        if os.path.exists(new_db):
            # let's delete the previous new database :
            os.remove(new_db)

    # let's compute the new names :
    olddb_connection = sqlite3.connect(get_database_fullname())
    olddb_connection.row_factory = sqlite3.Row
    olddb_cursor = olddb_connection.cursor()

    files, anomalies_nbr = action__rebase__files(olddb_cursor, dest_params, newtargetpath)

    go_on = True
    if anomalies_nbr != 0:
        go_on = False
        answer = \
            input(("\nAt least one anomaly detected (see details above) "
                   "Are you sure you want to go on ? (y/N) "))

        if answer in ("y", "yes"):
            go_on = True

    if not go_on:
        olddb_connection.close()
        return
    else:
        action__rebase__write(new_db, files)
        olddb_connection.close()

#///////////////////////////////////////////////////////////////////////////////
def action__rebase__files(olddb_cursor, dest_params, newtargetpath):
    """
        action__rebase__files()
        ________________________________________________________________________

        Return a dict of the files to be copied (old name, new name, ...) and
        the number of anomalies.

        Anomalies : files' names collisions.
        ________________________________________________________________________

        PARAMETER :
                o olddb_cursor         : cursor to the source database
                o dest_params          : an object returned by read_parameters_from_cfgfile(),
                                         like CFG_PARAMETERS
                o newtargetpath        : (str) path to the new target directory.

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
    for index, olddb_record in enumerate(olddb_cursor.execute('SELECT * FROM dbfiles')):
        fullname = normpath(os.path.join(source_path, olddb_record["name"]))
        filename_no_extens, extension = get_filename_and_extension(fullname)

        size = olddb_record["size"]
        date = olddb_record["sourcedate"]
        new_name = \
            create_target_name(parameters=dest_params,
                               hashid=olddb_record["hashid"],
                               filename_no_extens=filename_no_extens,
                               path=olddb_record["sourcename"],
                               extension=extension,
                               _size=size,
                               date=datetime.utcfromtimestamp(date).strftime(CST__DTIME_FORMAT),
                               database_index=index)
        new_name = normpath(os.path.join(newtargetpath, new_name))
        tagsstr = olddb_record["tagsstr"]

        LOGGER.info("      o %s : %s would be copied as %s",
                    olddb_record["hashid"], olddb_record["name"], new_name)

        if new_name in filenames:
            LOGGER.warning("      ! anomaly : ancient file %s should be renamed as %s "
                           "but this name would have been already created "
                           "in the new target directory ! ",
                           new_name, fullname)
            LOGGER.warning("        Two different files from the ancient target directory "
                           "can't bear the same name in the new target directory !")
            anomalies_nbr += 1
        elif os.path.exists(new_name):
            LOGGER.warning("      ! anomaly : ancient file %s should be renamed as %s "
                           "but this name already exists in new target directory !",
                           new_name, fullname)
            anomalies_nbr += 1
        else:
            files[olddb_record["hashid"]] = (fullname, new_name, date, tagsstr)
            filenames.add(new_name)

    return files, anomalies_nbr

#///////////////////////////////////////////////////////////////////////////////
def action__rebase__write(new_db, _files):
    """
        action__rebase__write()
        ________________________________________________________________________

        Write the files described by "_files" in the new target directory.
        ________________________________________________________________________

        PARAMETER :
                o new_db                : (str) new database's name
                o _files                : (dict) see action__rebase__files()

        About the underscore before "_files" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        no RETURNED VALUE
    """
    # let's write the new database :
    newdb_connection = sqlite3.connect(new_db)
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
            LOGGER.info("    o (%s/%s) adding a file in the new database", index+1, len(_files))
            LOGGER.info("      o hashid      : %s", futurefile_hashid)
            LOGGER.info("      o source name : \"%s\"", futurefile[0])
            LOGGER.info("      o desti. name : \"%s\"", futurefile[1])
            LOGGER.info("      o source date : %s", strdate)
            LOGGER.info("      o size        : %s", futurefile[4])
            LOGGER.info("      o tags        : \"%s\"", futurefile[3])

            if not ARGS.off:
                newdb_cursor.execute('INSERT INTO dbfiles VALUES (?,?,?,?,?,?,?)', file_to_be_added)
                newdb_connection.commit()

    except sqlite3.IntegrityError as exception:
        LOGGER.exception("!!! An error occured while writing the new database : ")
        raise KatalError("An error occured while writing the new database : "+str(exception))

    newdb_connection.close()

    # let's copy the files :
    for index, futurefile_hashid in enumerate(_files):
        futurefile = _files[futurefile_hashid]
        old_name, new_name = futurefile[0], futurefile[1]

        LOGGER.info("    o (%s/%s) copying \"%s\" as \"%s\"",
                    index+1, len(_files), old_name, new_name)
        if not ARGS.off:
            shutil.copyfile(old_name, new_name)

    LOGGER.info("    ... done")

#///////////////////////////////////////////////////////////////////////////////
def action__reset():
    """
        action__reset()
        ________________________________________________________________________

        Delete the files in the target directory and the database.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    LOGGER.info("    = about to delete (=move in the trash) the target files and the database.")

    if not os.path.exists(normpath(get_database_fullname())):
        LOGGER.warning("    ! no database found, nothing to do .")
        return

    if ARGS.verbosity != 'none':
        answer = \
            input(("\nDo you really want to delete (=move to the katal trash directory)"
                   "the files in the target directory and the database (y/N) "))
        if answer not in ("y", "yes"):
            return

    db_connection = sqlite3.connect(get_database_fullname())
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    files_to_be_removed = []  # a list of (hashid, fullname)
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        files_to_be_removed.append((db_record["hashid"], db_record["name"]))

    for hashid, name in files_to_be_removed:
        LOGGER.info("   o removing %s from the database and from the target path", name)
        if not ARGS.off:
            # let's remove the file from the target directory :
            shutil.move(os.path.join(normpath(ARGS.targetpath), name),
                        os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR, name))
            # let's remove the file from the database :
            db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (hashid,))

            db_connection.commit()

    db_connection.close()

    LOGGER.info("    = ... done : the database should be empty, "
                "the target files should no longer exist.")

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
    LOGGER.info("  = removing all files with no tags (=moving them to the trash).")

    if not os.path.exists(normpath(get_database_fullname())):
        LOGGER.warning("    ! no database found.")
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        files_to_be_removed = []    # list of (hashid, name)
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if db_record["tagsstr"] == "":
                files_to_be_removed.append((db_record["hashid"], db_record["name"]))

        if len(files_to_be_removed) == 0:
            LOGGER.warning("   ! no files to be removed.")
        else:
            for hashid, name in files_to_be_removed:
                LOGGER.info("   o removing %s from the database and from the target path", name)
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
def action__rmtags(dest):
    """
        action__rmtags()
        ________________________________________________________________________

        Remove the tags' string(s) in the target directory, overwriting ancient
        tags.
        ________________________________________________________________________

        PARAMETERS
                o dest           : (str) a regex string describing what files are
                                   concerned
    """
    LOGGER.info("  = let's remove the tags' string(s) in %s", dest)
    action__settagsstr(tagsstr="", dest=dest)

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
    LOGGER.info("  = selecting files according to the instructions in the config file...")

    LOGGER.info("  o the files will be copied in \"%s\" "
                "(path: \"%s\")", ARGS.targetpath, normpath(ARGS.targetpath))
    LOGGER.info("  o the files will be renamed according "
                "to the \"%s\" pattern.", CFG_PARAMETERS["target"]["name of the target files"])

    LOGGER.info("  o file list :")

    # let's initialize SELECT and SELECT_SIZE_IN_BYTES :
    number_of_discarded_files = fill_select()

    LOGGER.info("    o size of the selected file(s) : %s", size_as_str(SELECT_SIZE_IN_BYTES))

    if len(SELECT) == 0:
        LOGGER.warning("    ! no file selected ! "
                       "You have to modify the config file to get some files selected.")
    else:
        ratio = len(SELECT)/(len(SELECT)+number_of_discarded_files)*100.0
        LOGGER.info("    o number of selected files "
                    "(after discarding %s file(s)) : %s, "
                    "%.2f%% of the source files.",
                    len(SELECT), number_of_discarded_files, ratio)

    # let's check that the target path has sufficient free space :
    if CFG_PARAMETERS["target"]["mode"] != "nocopy":
        available_space = get_disk_free_space(ARGS.targetpath)
        if available_space > SELECT_SIZE_IN_BYTES*CST__FREESPACE_MARGIN:
            size_ok = "ok"
            colorconsole = "white"
        else:
            size_ok = "!!! problem !!!"
            colorconsole = "red"

        LOGGER.info("    o required space : %s; "
                    "available space on disk : %s (%s)",
                    size_as_str(SELECT_SIZE_IN_BYTES), size_as_str(available_space),
                    size_ok, color=colorconsole)

    # if there's no --add option, let's give some examples of the target names :
    if not ARGS.add and CFG_PARAMETERS["target"]["mode"] != "nocopy":
        example_index = 0
        for hashid in SELECT:

            complete_source_filename = SELECT[hashid].fullname

            target_name = os.path.join(normpath(ARGS.targetpath), SELECT[hashid].targetname)

            LOGGER.info("    o e.g. ... \"%s\" "
                        "would be copied as \"%s\" .", complete_source_filename, target_name)

            example_index += 1

            if example_index > 5:
                break

#///////////////////////////////////////////////////////////////////////////////
def action__settagsstr(tagsstr, dest):
    """
        action__settagsstr()
        ________________________________________________________________________

        Set the tags' string(s) in the target directory, overwriting ancient tags.
        ________________________________________________________________________

        PARAMETERS
                o tagsstr      : (str) the new tags' strings
                o dest         : (str) a regex string describing what files are
                                 concerned
    """
    LOGGER.info("  = let's apply the tag string\"%s\" to %s", tagsstr, dest)
    modify_the_tag_of_some_files(tag=tagsstr, dest=dest, mode="set")

#///////////////////////////////////////////////////////////////////////////////
def action__target_kill(filename):
    """
        action__target_kill()
        ________________________________________________________________________

        Delete "filename" from the target directory and from the database.
        ________________________________________________________________________

        PARAMETER
                o  filename    : (str) file's name to be deleted.
                                  DO NOT GIVE A PATH, just the file's name,
                                  without the path to the target directory

        RETURNED VALUE
                (int) : 0 if success, -1 if the file doesn't exist in the target
                        directory, -2 if the file doesn't exist in the database,
                        -3 if there's no database.
    """
    LOGGER.info("  = about to remove \"%s\" from the target directory (=file moved to the trash) "
                "and from its database =", filename)
    if not os.path.exists(os.path.join(normpath(ARGS.targetpath), filename)):
        LOGGER.warning("    ! can't find \"%s\" file on disk.", filename)
        return -1

    if not os.path.exists(normpath(get_database_fullname())):
        LOGGER.warning("    ! no database found.")
        return -3
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        filename_hashid = None
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if db_record["name"] == os.path.join(normpath(ARGS.targetpath), filename):
                filename_hashid = db_record["hashid"]

        if filename_hashid is None:
            LOGGER.warning("    ! can't find \"%s\" file in the database.", filename)
            res = -2
        else:
            if not ARGS.off:
                # let's remove filename from the target directory :
                shutil.move(os.path.join(normpath(ARGS.targetpath), filename),
                            os.path.join(normpath(ARGS.targetpath),
                                         CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR, filename))

                # let's remove filename from the database :
                db_cursor.execute("DELETE FROM dbfiles WHERE hashid=?", (filename_hashid,))

            res = 0  # success.

        db_connection.commit()
        db_connection.close()

        LOGGER.info("    ... done")
        return res

#///////////////////////////////////////////////////////////////////////////////
def action__whatabout(src):
    """
        action__whatabout()
        ________________________________________________________________________

        Take a look at the "src" file/directory and answer the following question :
        is this file/(are these files) already in the target directory ?
        ________________________________________________________________________

        PARAMETER
            o src : (str) the source file's name

        RETURNED VALUE : (bool)is everything ok (=no error) ?
    """
    #. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
    def show_infos_about_a_srcfile(srcfile_name):
        """
                Display the expected informations about a file named srcfile_name .
        """
        LOGGER.info("  = what about the \"%s\" file ? (path : \"%s\")", src, srcfile_name)
        size = os.stat(srcfile_name).st_size
        LOGGER.info("    = size : %s", size_as_str(size))

        sourcedate = datetime.utcfromtimestamp(os.path.getmtime(srcfile_name))
        sourcedate = sourcedate.replace(second=0, microsecond=0)
        sourcedate2 = sourcedate
        sourcedate2 -= datetime(1970, 1, 1)
        sourcedate2 = sourcedate2.total_seconds()
        LOGGER.info("    = mtime : %s (epoch value : %s)", sourcedate, sourcedate2)

        srchash = hashfile64(srcfile_name)
        LOGGER.info("    = hash : %s", srchash)

        # is the hash in the database ?
        already_present_in_db = False
        for hashid in TARGET_DB:
            if hashid == srchash:
                already_present_in_db = True
                break
        if already_present_in_db:
            LOGGER.info("    = the file's content is equal to a file "
                        "ALREADY present in the database.")
        else:
            LOGGER.info("    = the file isn't present in the database.")

    # (1) does src exist ?
    normsrc = normpath(src)
    if not os.path.exists(normsrc):
        LOGGER.warning("  ! error : can't find source file \"%s\" .", normsrc)
        return False

    # (2) is src a file or a directory ?
    if os.path.isdir(normsrc):
        # informations about the source directory :
        if normpath(ARGS.targetpath) in normsrc:
            LOGGER.warning("  ! error : the given directory is inside the target directory.")
            return False

        for dirpath, _, filenames in os.walk(normpath(src)):
            for filename in filenames:
                fullname = os.path.join(normpath(dirpath), filename)
                show_infos_about_a_srcfile(fullname)

    else:
        # informations about the source file :
        if normpath(ARGS.targetpath) in normpath(src):
            # special case : the file is inside the target directory :
            LOGGER.info("  = what about the \"%s\" file ? (path : \"%s\")", src, normsrc)
            LOGGER.info("    This file is inside the target directory.")
            srchash = hashfile64(normsrc)
            LOGGER.info("    = hash : %s", srchash)
            LOGGER.info("    Informations extracted from the database :")
            # informations from the database :
            db_connection = sqlite3.connect(get_database_fullname())
            db_connection.row_factory = sqlite3.Row
            db_cursor = db_connection.cursor()
            for db_record in db_cursor.execute("SELECT * FROM dbfiles WHERE hashid=?", (srchash,)):
                LOGGER.info("    = partial hashid : %s", db_record["partialhashid"])
                LOGGER.info("    = name : %s", db_record["name"])
                LOGGER.info("    = size : %s", db_record["size"])
                LOGGER.info("    = source name : %s", db_record["sourcename"])
                LOGGER.info("    = source date : %s", db_record["sourcedate"])
                LOGGER.info("    = tags' string : %s", db_record["tagsstr"])
            db_connection.close()

        else:
            # normal case : the file is outside the target directory :
            show_infos_about_a_srcfile(normpath(src))

    return True

#///////////////////////////////////////////////////////////////////////////////
def add_keywords_in_targetstr(srcstring,
                              hashid,
                              filename_no_extens,
                              path,
                              extension,
                              _size,
                              date,
                              database_index):
    """
        add_keywords_in_targetstr()
        ________________________________________________________________________

          The function replaces some keywords in the string by the parameters given
        to this function.
          The function returned a string which may be used to create target files.

        see the available keywords in the documentation.
            (see documentation:configuration file)
        ________________________________________________________________________

        PARAMETERS
                o srcstring                    : (str)
                o hashid                       : (str)
                o filename_no_extens           : (str)
                o path                         : (str
                o extensiont : in the .ini files, '%' have to be written twice (as in
                                 '%%p', e.g.) but Python reads it as if only one % was
                                                  written.
                                                  : (str)
                o _size                        : (int)
                o date                         : (str) see CST__DTIME_FORMAT
                o database_index               : (int)

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        RETURNED VALUE
                (str)the expected string
    """
    res = srcstring

    # beware : order matters !
    res = res.replace("%ht",
                      hex(int(datetime.strptime(date,
                                                CST__DTIME_FORMAT).timestamp()))[2:])

    res = res.replace("%h", hashid)

    res = res.replace("%ff", remove_illegal_characters(filename_no_extens))
    res = res.replace("%f", filename_no_extens)

    res = res.replace("%pp", remove_illegal_characters(path))
    res = res.replace("%p", path)

    res = res.replace("%ee", remove_illegal_characters(extension))
    res = res.replace("%e", extension)

    res = res.replace("%s", str(_size))

    res = res.replace("%dd", remove_illegal_characters(date))

    res = res.replace("%t",
                      str(int(datetime.strptime(date,
                                                CST__DTIME_FORMAT).timestamp())))

    res = res.replace("%i",
                      remove_illegal_characters(str(database_index)))

    return res

#///////////////////////////////////////////////////////////////////////////////
def configure_loggers():
    """
        configure_loggers()
        ________________________________________________________________________

        Configure loggers to write to the correct files and to the console.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    #...........................................................................
    # to the log files :
    if USE_LOGFILE:

        try:
            handler1 = RotatingFileHandler(
                get_logfile_fullname(),
                # int(float) to allow to write 1e6 in the config file
                maxBytes=int(float(CFG_PARAMETERS["log file"]["maximal size"])),
                backupCount=CFG_PARAMETERS.getint('log file', 'backup count'))

            formatter1 = logging.Formatter('%(levelname)s::%(asctime)s::  %(message)s')
            handler1.setFormatter(formatter1)

            if ARGS.verbosity == 'none':
                handler1.setLevel(logging.INFO) # To keep a record of what is done
            elif ARGS.verbosity == 'normal':
                handler1.setLevel(logging.INFO)
            elif ARGS.verbosity == 'high':
                handler1.setLevel(logging.DEBUG)

            LOGGER.addHandler(handler1)
            FILE_LOGGER.addHandler(handler1)

        except FileNotFoundError as exception:
            print("  ! Beware, the log file can't be opened : the log messages will be displayed")
            print("  ! to the console and will not be stored in log files. THAT'S SURELY NOT")
            print("  ! WHAT YOU WANT TO DO.")
            print("  ! It's typically because the path to the log file doesn't exist.")
            print("  ! Python's message : ", exception)

    #...........................................................................
    # to the console :
    formatter2 = ColorFormatter('%(color_start)s%(message)s%(color_end)s')

    handler2 = logging.StreamHandler()
    handler2.setFormatter(formatter2)

    if ARGS.verbosity == 'none':
        handler2.setLevel(logging.ERROR)
    elif ARGS.verbosity == 'normal':
        handler2.setLevel(logging.INFO)
    elif ARGS.verbosity == 'high':
        handler2.setLevel(logging.DEBUG)

    LOGGER.addHandler(handler2)

    #...........................................................................
    # setting the threshold for each handler :
    # see https://docs.python.org/3.5/library/logging.html
    FILE_LOGGER.setLevel(logging.DEBUG)
    LOGGER.setLevel(logging.DEBUG)

#///////////////////////////////////////////////////////////////////////////////
def create_empty_db(db_name):
    """
        create_empty_db()
        ________________________________________________________________________

        Create an empty database named db_name .
        ________________________________________________________________________

        PARAMETER :
            o db_name : name of the file to be created .
                         Please use a normpath'd parameter : the normpath function
                         will not be called by create_empty_db() !

        no RETURNED VALUE
    """
    LOGGER.info("  ... creating an empty database named \"%s\"...", db_name)

    if not ARGS.off:

        db_connection = sqlite3.connect(db_name)
        db_cursor = db_connection.cursor()

        db_cursor.execute(CST__SQL__CREATE_DB)

        db_connection.commit()
        db_connection.close()

    LOGGER.info("   ... database created")

#///////////////////////////////////////////////////////////////////////////////
def create_subdirs_in_target_path():
    """
        create_subdirs_in_target_path()
        ________________________________________________________________________

        Create the expected subdirectories in ARGS.targetpath .

        No log messages for this function, everything is printed to the console.
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
        if not os.path.exists(normpath(fullpath)) and not ARGS.off:
            print("  * Since the {0} path \"{1}\" (path : \"{2}\") "
                  "doesn't exist, let's create it.".format(name,
                                                           fullpath,
                                                           normpath(fullpath)))
            os.mkdir(normpath(fullpath))

#/////////////////////////////////////////////////////////////////////////////////////////
def create_target_name(parameters,
                       hashid,
                       filename_no_extens,
                       path,
                       extension,
                       _size,
                       date,
                       database_index):
    """
        create_target_name()
        ________________________________________________________________________

        Create the name of a file (a target file) from various informations
        given by the parameters. The function reads the string stored in
        parameters["target"]["name of the target files"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o parameters                   : an object returned by
                                                  read_parameters_from_cfgfile(),
                                                  like CFG_PARAMETERS
                o hashid                       : (str)
                o filename_no_extens           : (str)
                o path                         : (str
                o extension                    : (str)
                o _size                        : (int)
                o date                         : (str) see CST__DTIME_FORMAT
                o database_index               : (int)

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        RETURNED VALUE
                (str)name
    """
    return(add_keywords_in_targetstr(srcstring=parameters["target"]["name of the target files"],
                                     hashid=hashid,
                                     filename_no_extens=filename_no_extens,
                                     path=path,
                                     extension=extension,
                                     _size=_size,
                                     date=date,
                                     database_index=database_index))

#/////////////////////////////////////////////////////////////////////////////////////////
def create_target_name_and_tags(parameters,
                                hashid,
                                filename_no_extens,
                                path,
                                extension,
                                _size,
                                date,
                                database_index):
    """
        create_target_name_and_tags()
        ________________________________________________________________________

        Create the name of a file (a target file) from various informations
        given by the parameters. The function reads the string stored in
        parameters["target"]["name of the target files"] and in
        parameters["target"]["tags"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o parameters                   : an object returned by
                                                 read_parameters_from_cfgfile(),
                                                 like CFG_PARAMETERS
                o hashid                       : (str)
                o filename_no_extens           : (str)
                o path                         : (str
                o extension                    : (str)
                o _size                        : (int)
                o date                         : (str) see CST__DTIME_FORMAT
                o database_index               : (int)

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        RETURNED VALUE
                ( (str)name, (str)tags )
    """
    name = create_target_name(parameters,
                              hashid,
                              filename_no_extens,
                              path,
                              extension,
                              _size,
                              date,
                              database_index)

    tags = create_target_name(parameters,
                              hashid,
                              filename_no_extens,
                              path,
                              extension,
                              _size,
                              date,
                              database_index)
    return (name, tags)

#/////////////////////////////////////////////////////////////////////////////////////////
def create_target_tags(parameters,
                       hashid,
                       filename_no_extens,
                       path,
                       extension,
                       _size,
                       date,
                       database_index):
    """
        create_target_tags()
        ________________________________________________________________________

        Create the tags of a file (a target file) from various informations
        given by the parameters. The function reads the string stored in
        parameters["target"]["tags"] and replaces some
        keywords in the string by the parameters given to this function.

        see the available keywords in the documentation.
            (see documentation:configuration file)

        caveat : in the .ini files, '%' have to be written twice (as in
                 '%%p', e.g.) but Python reads it as if only one % was
                 written.
        ________________________________________________________________________

        PARAMETERS
                o parameters                   : an object returned by
                                                 read_parameters_from_cfgfile(),
                                                 like CFG_PARAMETERS
                o hashid                       : (str)
                o filename_no_extens           : (str)
                o path                         : (str
                o extension                    : (str)
                o _size                        : (int)
                o date                         : (str) see CST__DTIME_FORMAT
                o database_index               : (int)

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        RETURNED VALUE
                (str)name
    """
    return(add_keywords_in_targetstr(srcstring=parameters["target"]["tags"],
                                     hashid=hashid,
                                     filename_no_extens=filename_no_extens,
                                     path=path,
                                     extension=extension,
                                     _size=_size,
                                     date=date,
                                     database_index=database_index))

#///////////////////////////////////////////////////////////////////////////////
def draw_table(rows, data):
    """
        draw_table()
        ________________________________________________________________________

        Draw a table with some <_rows> and fill it with _data. The output is
        created by calling the LOGGER.info() function.
        ________________________________________________________________________

        PARAMETERS :
            o rows : list of ( (str)row_name,
                               (int)max length for this row,
                               (str)separator,
                             )

                   e.g. :
                   rows= ( ("hashid", HASHID_MAXLENGTH, "|"), )

            o  data : ( (str)row_content1, (str)row_content2, ...)

        no RETURNED VALUE
    """

    #...........................................................................
    def draw_line():
        " draw a simple line made of + and -"
        string = " "*6 + "+"
        for _, row_maxlength, _ in rows:
            string += "-"*(row_maxlength+2) + "+"
        LOGGER.info(string)

    # real rows' widths : it may happen that a row's width is greater than
    # the maximal value given in rows since the row name is longer than
    # this maximal value.
    _rows = []
    for row_name, row_maxlength, row_separator in rows:
        _rows.append((row_name, max(len(row_name), row_maxlength), row_separator))

    # header :
    draw_line()

    string = " "*6 + "|"
    for row_name, row_maxlength, row_separator in _rows:
        string += " " + row_name + " "*(row_maxlength-len(row_name)+1) + row_separator
    LOGGER.info(string)

    draw_line()

    # data :
    for linedata in data:
        string = "      |"
        for row_index, row_content in enumerate(linedata):
            text = shortstr(row_content, rows[row_index][1])
            string += (" " + text + \
                       " "*(rows[row_index][1]-len(text)) + \
                       " " + rows[row_index][2])
        LOGGER.info(string)  # let's write the computed line

    draw_line()

#///////////////////////////////////////////////////////////////////////////////
def eval_filters(filters):
    """
    eval_filters(list_ of_filters) -> Filter()
    ________________________________________________________________________

    Evaluate the eval string from config.
    Return a Filter instance which return True if a file can be selected
    according filters definition and can be selected.
    Called from read_filters()
    ________________________________________________________________________

    PARAMETERS
            o filters : (list) list of defined filters

    RETURNED VALUE
            A Filter instance, corresponding to the eval string and filters
            conditions.

    """
    evalstr = CFG_PARAMETERS["source"]["eval"]

    try:
        # eval() IS a dangerous function : see for example
        # http://nedbatchelder.com/blog/201206/eval_really_is_dangerous.html
        if '__' in evalstr:
            raise KatalError("Error in configuration file : trying to compute "
                             'the "{0}" string; double underscore (__) '
                             "are not allowed".format(evalstr))

        return eval(evalstr, {'__builtins__': {}}, filters)

    except Exception as exception:
        raise KatalError("The eval formula in the config file (\"{0}\")"
                         "contains an error. Python message : \"{1}\"".format(evalstr,
                                                                              exception))

#///////////////////////////////////////////////////////////////////////////////
def fill_select(debug_datatime=None):
    """
        fill_select()
        ________________________________________________________________________

        Fill SELECT and SELECT_SIZE_IN_BYTES from the files stored in
        the source path. This function is used by action__select() .
        ________________________________________________________________________

        PARAMETERS
                o debug_datatime : None (normal value) or a dict of CST__DTIME_FORMAT
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
            fullname = os.path.join(dirpath, filename)

            # ..................................................................
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link on the
            #   "size = os.stat(normpath(fullname)).st_size" line (see below).
            # ..................................................................
            if not os.path.exists(fullname):
                LOGGER.warning("    ! browsing %s, an error occured : "
                               "can't read the file \"%s\"", source_path, fullname)

            else:
                fname_no_extens, extension = get_filename_and_extension(normpath(filename))

                # if we know the total amount of files to be selected (see the --infos option),
                # we can add the percentage done :
                prefix = ""
                if INFOS_ABOUT_SRC_PATH[1] is not None and INFOS_ABOUT_SRC_PATH[1] != 0:
                    prefix = "[{0:.4f}%]".format(file_index / INFOS_ABOUT_SRC_PATH[1] * 100.0)

                # ..................................................................
                # what should we do with 'filename' ?
                # ..................................................................
                if not FILTER(fullname):
                    # ... nothing : incompatibility with at least one filter :
                    number_of_discarded_files += 1

                    if ARGS.verbosity == 'high':
                        LOGGER.info("    - %s discarded \"%s\" "
                                    ": incompatibility with the filter(s)",
                                    prefix, fullname)
                else:
                    size = os.stat(fullname).st_size
                    time = datetime.fromtimestamp(os.stat(fullname).st_mtime)

                    # 'filename' being compatible with the filters, let's try
                    # to add it in the datase :
                    tobeadded, partialhashid, hashid = thefilehastobeadded__db(fullname, size)

                    if tobeadded and hashid in SELECT:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # tobeadded is True but hashid is already in SELECT; let's discard
                        # <filename> :
                        number_of_discarded_files += 1

                        if ARGS.verbosity == 'high':
                            LOGGER.info("    - %s (similar hashid among the files to be copied, "
                                        "in the source directory) discarded \"%s\"",
                                        prefix, fullname)

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
                                          create_target_name(parameters=CFG_PARAMETERS,
                                                             hashid=hashid,
                                                             filename_no_extens=fname_no_extens,
                                                             path=dirpath,
                                                             extension=extension,
                                                             _size=size,
                                                             date=time.strftime(CST__DTIME_FORMAT),
                                                             database_index=len(TARGET_DB) + \
                                                                             len(SELECT)),
                                       targettags= \
                                          create_target_tags(parameters=CFG_PARAMETERS,
                                                             hashid=hashid,
                                                             filename_no_extens=fname_no_extens,
                                                             path=dirpath,
                                                             extension=extension,
                                                             _size=size,
                                                             date=time.strftime(CST__DTIME_FORMAT),
                                                             database_index=len(TARGET_DB) + \
                                                                             len(SELECT)))

                        LOGGER.info("    + %s selected \"%s\" (file selected #%s)",
                                    prefix, fullname, len(SELECT))
                        LOGGER.info("       size=%s; date=%s",
                                    size, time.strftime(CST__DTIME_FORMAT))

                        SELECT_SIZE_IN_BYTES += size

                    else:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # tobeadded is False : let's discard <filename> :
                        number_of_discarded_files += 1

                        if ARGS.verbosity == 'high':
                            LOGGER.info("    - %s (similar hashid in the database) "
                                        " discarded \"%s\"", prefix, fullname)


    return fill_select__checks(number_of_discarded_files=number_of_discarded_files,
                               prefix=prefix,
                               fullname=fullname)

#///////////////////////////////////////////////////////////////////////////////
def fill_select2(debug_datatime=None):
    """
        fill_select()
        ________________________________________________________________________

        Fill SELECT and SELECT_SIZE_IN_BYTES from the files stored in
        the source path. This function is used by action__select() .
        ________________________________________________________________________

        PARAMETERS
                o debug_datatime : None (normal value) or a dict of CST__DTIME_FORMAT
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
            fullname = os.path.join(dirpath, filename)

            # ..................................................................
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link on the
            #   "size = os.stat(normpath(fullname)).st_size" line (see below).
            # ..................................................................
            if not os.path.exists(fullname):
                LOGGER.warning("    ! browsing %s, an error occured : "
                               "can't read the file \"%s\"", source_path, fullname)

            else:

                # if we know the total amount of files to be selected (see the --infos option),
                # we can add the percentage done :
                prefix = ""
                if INFOS_ABOUT_SRC_PATH[1] is not None and INFOS_ABOUT_SRC_PATH[1] != 0:
                    prefix = "[{0:.4f}%]".format(file_index / INFOS_ABOUT_SRC_PATH[1] * 100.0)

                # ..................................................................
                # what should we do with 'filename' ?
                # ..................................................................
                if not FILTER(fullname):
                    # ... nothing : incompatibility with at least one filter :
                    number_of_discarded_files += 1

                    if ARGS.verbosity == 'high':
                        LOGGER.info("    - %s discarded \"%s\" "
                                    ": incompatibility with the filter(s)",
                                    prefix, fullname)
                else:
                    element = SelectElement(fullname)
                    # 'filename' being compatible with the filters, let's try
                    # to add it in the datase :
                    tobeadded = thefilehastobeadded__db(element)

                    if tobeadded and hashid in SELECT:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # tobeadded is True but hashid is already in SELECT; let's discard
                        # <filename> :
                        number_of_discarded_files += 1

                        if ARGS.verbosity == 'high':
                            LOGGER.info("    - %s (similar hashid among the files to be copied, "
                                        "in the source directory) discarded \"%s\"",
                                        prefix, fullname)

                    elif tobeadded:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # ok, let's add <filename> to SELECT...
                        SELECT[element.hashid] = element

                        LOGGER.info("    + %s selected \"%s\" (file selected #%s)",
                                    prefix, fullname, len(SELECT))
                        LOGGER.info("       size=%s; date=%s",
                                    element.size, element.date)


                    else:
                        # . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
                        # tobeadded is False : let's discard <filename> :
                        number_of_discarded_files += 1

                        if ARGS.verbosity == 'high':
                            LOGGER.info("    - %s (similar hashid in the database) "
                                        " discarded \"%s\"", prefix, fullname)


    return fill_select__checks(number_of_discarded_files=number_of_discarded_files,
                               prefix=prefix,
                               fullname=fullname)

#///////////////////////////////////////////////////////////////////////////////
def fill_select__checks(number_of_discarded_files, prefix, fullname):
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
                o number_of_discarded_files    : (int) see fill_select()
                o prefix                       : (str) see fill_select()
                o fullname                     : (str) see fill_select()

        RETURNED VALUE
                (int) the number of discarded files
    """
    LOGGER.info("    o checking that there's no anomaly with the selected files...")

    # (1) future filename's can't be in conflict with another file in SELECT
    LOGGER.info("       ... let's check that future filenames aren't in conflict "
                "with another file in SELECT...")
    to_be_discarded = []        # a list of hash.
    for (selectedfile_hash1, selectedfile_hash2) in itertools.combinations(SELECT, 2):

        if SELECT[selectedfile_hash1].targetname == SELECT[selectedfile_hash2].targetname:
            LOGGER.warning("    ! %s discarded \"%s\" : target filename \"%s\" would be used "
                           "two times for two different files !",
                           prefix, fullname, SELECT[selectedfile_hash2].targetname)

            to_be_discarded.append(selectedfile_hash2)

    # (2) future filename's can't be in conflict with another file already
    # stored in the target path :
    if not CFG_PARAMETERS["target"]["mode"] == 'nocopy':
        LOGGER.info("       ... let's check that future filenames aren't in conflict "
                    "with another file already")
        LOGGER.info("           stored in the target path...")
        for selectedfile_hash in SELECT:
            if os.path.exists(os.path.join(normpath(ARGS.targetpath),
                                           SELECT[selectedfile_hash].targetname)):
                LOGGER.warning("    ! %s discarded \"%s\" : target filename \"%s\" already "
                               "exists in the target path !",
                               prefix, fullname, SELECT[selectedfile_hash].targetname)

                to_be_discarded.append(selectedfile_hash)

    # final message and deletion :
    if len(to_be_discarded) == 0:
        LOGGER.info("    o  everything ok : no anomaly detected. See details above.")
    else:
        if len(to_be_discarded) == 1:
            ending = "y"
        else:
            ending = "ies"
        LOGGER.warning("    !  beware : %s anomal%s detected. "
                       "See details above.", len(to_be_discarded), ending)

        for _hash in to_be_discarded:
            # e.g. , _hash may have discarded two times (same target name + file
            # already present on disk), hence the following condition :
            if _hash in SELECT:
                del SELECT[_hash]
                number_of_discarded_files += 1

    return number_of_discarded_files

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
def get_disk_free_space(path):
    """
        get_disk_free_space()
        ________________________________________________________________________

        return the available space on disk() in bytes. Code for Windows system
        from http://stackoverflow.com/questions/51658/ .
        ________________________________________________________________________

        PARAMETER
                o path : (str) the source path belonging to the disk to be
                          analysed.

        RETURNED VALUE
                the expected int(eger)
    """
    if CST__PLATFORM == 'Windows':
        free_bytes = ctypes.c_ulonglong(0)
        ctypes.windll.kernel32.GetDiskFreeSpaceExW(ctypes.c_wchar_p(path),
                                                   None, None, ctypes.pointer(free_bytes))
        return free_bytes.value
    else:
        stat = os.statvfs(normpath(path))
        return stat.f_bavail * stat.f_frsize

#///////////////////////////////////////////////////////////////////////////////
def get_filename_and_extension(path):
    """
        get_filename_and_extension()
        ________________________________________________________________________

        Return
        ________________________________________________________________________

        PARAMETERS
                o  path        : (str) the source path

        RETURNED VALUE
                (str)filename without extension, (str)the extension without the
                initial dot.
    """
    fname_no_extens, extension = os.path.splitext(path)

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
def goodbye(timestamp_start):
    """
        goodbye()
        ________________________________________________________________________

        display a goodbye message.
        ________________________________________________________________________

        PARAMETER :
                o  timestamp_start : a datetime.datetime object

        no RETURNED VALUE
    """
    LOGGER.info("=== exit (Katal stopped at %s; "
                "total duration time : %s) ===",
                datetime.now().strftime(CST__DTIME_FORMAT), datetime.now() - timestamp_start)

#///////////////////////////////////////////////////////////////////////////////
def hashfile64(filename, stop_after=None):
    """
        hashfile64()
        ________________________________________________________________________

        return the footprint of a file, encoded with the base 64. If stop_after
        is set to an integer, only the beginning of the file will be used to
        compute the hash (see CST__PARTIALHASHID_BYTESNBR constant).
        ________________________________________________________________________

        PARAMETER
                o filename : (str) file's name
                o stop_after:(None/int) if None, the file will be entirely read,
                              otherwise, only the first stop_after bytes will
                              be read.
        RETURNED VALUE
                the expected string. If you use sha256 as a hasher, the
                resulting string will be 44 bytes long. E.g. :
                        "YLkkC5KqwYvb3F54kU7eEeX1i1Tj8TY1JNvqXy1A91A"
    """
    # hasher used by the hashfile64() function.
    hasher = hashlib.sha256()

    nbr_of_bytes_read = 0
    with open(filename, "rb") as afile:
        # a buffer of 65536 bytes is an optimized buffer.
        buf = afile.read(65536)
        while len(buf) > 0:
            nbr_of_bytes_read += 65536
            if stop_after is not None and nbr_of_bytes_read >= stop_after:
                break

            hasher.update(buf)
            buf = afile.read(65536)

    return b64encode(hasher.digest()).decode()

#///////////////////////////////////////////////////////////////////////////////
def is_ntfs_prefix_mandatory(path):
    """
        is_ntfs_prefix_mandatory()
        ________________________________________________________________________

        Return True if the path is a path in a systemfile requiring the NTFS
        prefix for long filenames.
        ________________________________________________________________________

        PARAMETER
            path : (str)the path to be tested

        RETURNED VALUE
            a boolean
    """
    longpath1 = os.path.join(path, "a"*250)
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
def main(args=None):
    """
        main()
        ________________________________________________________________________

        Main entry point.
        ________________________________________________________________________

        PARAMETER:
            o list(args) (Optionnal, default=None): the list of arguments to
              parse from the command line. If None, the arguments are taken from
              sys.argv.
              Mainly for tests

        no RETURNED VALUE

        This function should NOT have arguments : otherwise, the entrypoint
        defined in setup.py would not be valid.

        o  sys.exit(-1) is called if the config file is ill-formed.
        o  sys.exit(-2) is called if a KatalError exception is raised
        o  sys.exit(-3) is called if another exception is raised
    """
    global ARGS, CONFIG

    timestamp_start = datetime.now()

    try:
        CONFIG = Config()
        ARGS = CONFIG.read_command_line_arguments(args)

        main_warmup(timestamp_start)
        main_actions_tags()
        main_actions()

        goodbye(timestamp_start)

    except KatalError as exception:
        if LOGGER:
            LOGGER.exception("(%s) ! a critical error occured.\n"
                             "Error message : %s", __projectname__, exception)
        else:
            print("({0}) ! a critical error occured.\n"
                  "Error message : {1}".format(__projectname__, exception))
        sys.exit(-2)
    else:
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
                input("\nDo you want to update the target database and to {0} the selected "
                      "files into the target directory "
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
        action__downloadefaultcfg(targetname=CST__DEFAULT_CONFIGFILE_NAME,
                                  location=ARGS.downloaddefaultcfg)

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
def main_warmup(timestamp_start):
    """
        main_warmup()
        ________________________________________________________________________

        Initializations :

            if the --new/--downloaddefaultcfg options have not be used :

            o welcome()
            o configfile_name = None / a string
            o reading of the configuration file
            o list of the expected directories : if one directory is missing, let's create it.
              create_subdirs_in_target_path()
            o configure_loggers()
            o welcome_in_logfile()
            o warning if source path == target path
            o --infos
            o -si / --sourceinfos
            o -ti / --targetinfos
        ________________________________________________________________________

        PARAMETER :
                o timestamp_start : a datetime.datetime object

        no RETURNED VALUE

        o  sys.exit(-1) is called if the expected config file is ill-formed or missing.
    """
    global CFG_PARAMETERS

    #...........................................................................
    welcome(timestamp_start)

    #...........................................................................
    # a special case : if the options --new//--downloaddefaultcfg have been used, let's quit :
    if ARGS.new is not None or ARGS.downloaddefaultcfg is not None:
        return

    #...........................................................................
    # let's read the config files:
    try:
        CONFIG.read_config()
        CFG_PARAMETERS = CONFIG
    except configparser.Error:
        # ill-formed config file :
        print("  ! Error while reading config files, aborting.")
        sys.exit(-1)
    else:
        #.......................................................................
        # list of the expected directories : if one directory is missing, let's
        # create it. Required to do that before initialising loggers in case
        # the .katal/logs folder doesn't exist
        create_subdirs_in_target_path()

        # Logger initialisation :
        configure_loggers()
        welcome_in_logfile(timestamp_start)

    if CFG_PARAMETERS["target"]["mode"] == 'move':
        LOGGER.warning("  = 'move' mode")
        LOGGER.warning("  =     the files will be moved (NOT copied) in the target directory")

    if CFG_PARAMETERS["target"]["mode"] == 'nocopy':
        LOGGER.warning("  = 'nocopy' mode")
        LOGGER.warning("  =     the files will NOT be copied or moved in the target directory")

    source_path = CFG_PARAMETERS["source"]["path"]

    #...........................................................................
    if ARGS.targetpath == source_path:
        LOGGER.warning("  ! warning : "
                       "source path and target path have the same value, "
                       "namely \"%s\" (path: \"%s\")", ARGS.targetpath, normpath(ARGS.targetpath))

    #...........................................................................
    # we show the following informations :
    for path, info in ((CONFIG.cfg_files, "config file"),
                       (os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR), "trash subdir"),
                       (os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TASKS_SUBSUBDIR), "tasks subdir"),
                       (os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR), "log subdir"),):
        LOGGER.debug("  = let's use \"%s\" as %s", path, info)

    LOGGER.debug("  = source directory : \"%s\" (path : \"%s\")",
                 source_path, normpath(source_path))

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
def modify_the_tag_of_some_files(tag, dest, mode):
    """
        modify_the_tag_of_some_files()
        ________________________________________________________________________

        Modify the tag(s) of some files.
        ________________________________________________________________________

        PARAMETERS
                o tag          : (str) new tag(s)
                o dest         : (str) a string (wildcards accepted) describing
                                  what files are concerned
                o mode         : (str) "append" to add "tag" to the other tags
                                       "set" to replace old tag(s) by a new one
    """
    if not os.path.exists(normpath(get_database_fullname())):
        LOGGER.warning("    ! no database found.")
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        files_to_be_modified = []       # a list of (hashids, name)
        for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
            if fnmatch.fnmatch(db_record["name"], dest):
                files_to_be_modified.append((db_record["hashid"], db_record["name"]))

        if len(files_to_be_modified) == 0:
            LOGGER.info("    * no files match the given name(s) given as a parameter.")
        else:
            # let's apply the tag(s) to the <files_to_be_modified> :
            for hashid, filename in files_to_be_modified:

                LOGGER.info("    o applying the tag string \"%s\" to %s.", tag, filename)

                if ARGS.off:
                    pass

                elif mode == "set":
                    sqlorder = 'UPDATE dbfiles SET tagsstr=? WHERE hashid=?'
                    db_connection.execute(sqlorder, (tag, hashid))

                elif mode == "append":
                    sqlorder = ('UPDATE dbfiles SET tagsstr = tagsstr || \"{0}{1}\" '
                                'WHERE hashid=\"{2}\"').format(CST__TAG_SEPARATOR, tag, hashid)
                    db_connection.executescript(sqlorder)

                else:
                    raise KatalError("mode argument \"{0}\" isn't known".format(mode))

            db_connection.commit()

        db_connection.close()

#///////////////////////////////////////////////////////////////////////////////
def normpath(path):
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

        PARAMETER : (str)path

        RETURNED VALUE : the expected strinc
    """
    res = os.path.normpath(os.path.abspath(os.path.expanduser(path)))

    if ARGS.usentfsprefix:
        res = res.replace("\\\\?\\", "")

    if res == ".":
        res = os.getcwd()

    if ARGS.usentfsprefix:
        res = "\\\\?\\"+res

    return res

#///////////////////////////////////////////////////////////////////////////////
def read_filters():
    """
        read_filters()
        ________________________________________________________________________

        Initialize FILTERS from the configuration file.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    global FILTER

    filters = {}
    for section in CFG_PARAMETERS:
        if section.startswith('source.filter'):
            name = section[len('source.'):]
            filters[name] = Filter(CFG_PARAMETERS[section], name=name)

    FILTER = eval_filters(filters)

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
def remove_illegal_characters(src):
    """
        remove_illegal_characters()
        ________________________________________________________________________

        Replace some illegal characters by the underscore character. Use this function
        to create files on various plateforms.
        ________________________________________________________________________

        PARAMETER
                o src   : (str) the source string

        RETURNED VALUE
                the expected string, i.e. <src> without illegal characters.
    """
    res = src
    for char in ("*", "/", "\\", ".", "[", "]", ":", ";", "|", "=", ",", "?", "<", ">", "-", " "):
        res = res.replace(char, "_")
    return res

#///////////////////////////////////////////////////////////////////////////////
def shortstr(string, max_length):
    """
        shortstr()
        ________________________________________________________________________

        The function returns a shortened version of a string.
        ________________________________________________________________________

        PARAMETER
                o string          : (src) the source string
                o max_length   : (int) the maximal length of the string

        RETURNED VALUE
                the expected string
    """
    if len(string) > max_length:
        return "[...]"+string[-(max_length-5):]
    return string

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

    LOGGER.info("  = informations about the \"%s\" "
                "(path: \"%s\") source directory =", source_path, normpath(source_path))

    if not os.path.exists(normpath(source_path)):
        LOGGER.warning("    ! can't find source path \"%s\" .", source_path)
        return
    if not os.path.isdir(normpath(source_path)):
        LOGGER.warning("    ! source path \"%s\" isn't a directory .", source_path)
        return

    if is_ntfs_prefix_mandatory(source_path):
        LOGGER.warning("    ! the source path should be used "
                       "with the NTFS prefix for long filenames.")

        if not ARGS.usentfsprefix:
            LOGGER.warning("    ! ... but the --usentfsprefix argument wasn't given !")
            LOGGER.warning("    ! You may encounter an IOError, or a FileNotFound error.")
            LOGGER.warning("    ! If so, please use the --usentfsprefix argument.")
            LOGGER.warning("")

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
                    LOGGER.info("    ... already %s files read in the source directory, "
                                "still processing...", files_number_interval)
                    files_number_interval = 0
            else:
                LOGGER.warning("    ! browsing %s, an error occured : "
                               "can't read the file ", source_path, color='red')
                LOGGER.warning("    \"%s\"", fullname, color='red')

    LOGGER.info("    o files number : %s file(s)", files_number)
    LOGGER.info("    o total size : %s", size_as_str(total_size))
    LOGGER.info("    o list of all extensions (%s extension(s) found): ", len(extensions))

    for extension in sorted(extensions, key=lambda s: s.lower()):
        LOGGER.info("      - %15s : %s files, %s",
                    extension, extensions[extension][0], size_as_str(extensions[extension][1]))

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
    LOGGER.info("  = informations about the \"%s\" "
                "(path: \"%s\") target directory =",
                ARGS.targetpath, normpath(ARGS.targetpath))

    #...........................................................................
    if is_ntfs_prefix_mandatory(ARGS.targetpath):
        LOGGER.warning("    ! the target path should be used "
                       "with the NTFS prefix for long filenames.")

        if not ARGS.usentfsprefix:
            LOGGER.warning("    ! ... but the --usentfsprefix argument wasn't given !")
            LOGGER.warning("    ! You may encounter an IOError, or a FileNotFound error.")
            LOGGER.warning("    ! If so, please use the --usentfsprefix argument.")

    #...........................................................................
    if not os.path.exists(normpath(ARGS.targetpath)):
        LOGGER.warning("Can't find target path \"%s\".", ARGS.targetpath)
        return -1

    if not os.path.isdir(normpath(ARGS.targetpath)):
        LOGGER.warning("target path \"%s\" isn't a directory.", ARGS.targetpath)
        return -1

    if not os.path.exists(os.path.join(normpath(ARGS.targetpath),
                                       CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)):
        LOGGER.warning("    o no database in the target directory.")
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
        LOGGER.warning("    ! (empty database)")
        return 0

    LOGGER.info("    o %s file(s) in the database :", row_index)

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
        draw_table(rows=(("hashid/base64", hashid_maxlength, "|"),
                         ("name", targetname_maxlength, "|"),
                         ("tags", tagsstr_maxlength, "|"),
                         ("source name", sourcename_maxlength, "|"),
                         ("source date", CST__DTIME_FORMAT_LENGTH, "|")),
                   data=rows_data)
    else:
        draw_table(rows=(("hashid/base64", hashid_maxlength, "|"),
                         ("tags", tagsstr_maxlength, "|"),
                         ("source name", sourcename_maxlength, "|"),
                         ("source date", CST__DTIME_FORMAT_LENGTH, "|")),
                   data=rows_data)

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

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        About the multiples of bytes, see e.g. https://en.wikipedia.org/wiki/Megabyte .

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
def tagsstr_repr(tagsstr):
    """
        tagsstr_repr()
        ________________________________________________________________________

        Improve the way a tags' string can be displayed.
        ________________________________________________________________________

        PARAMETER
            tagsstr : the raw tags' string

        RETURNED VALUE
            the expected (str)string
    """
    if tagsstr.startswith(CST__TAG_SEPARATOR):
        # let's remove the first tag separator :
        return tagsstr[1:]
    else:
        return tagsstr

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__db(filename, _size):
    """
        thefilehastobeadded__db()
        ________________________________________________________________________

        Return True if the file isn't already known in the database.
        ________________________________________________________________________

        PARAMETERS
                o filename     : (str) file's name
                o _size         : (int) file's size, in bytes.

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        RETURNED VALUE
                either (False, None, None)
                either (True, partial hashid, hashid)
    """
    # (1) hont(datetime.strptime(date, CST__DTIME_FORMAT))w many file(s) in the database have a size equal to _size ?
    # a list of hashid(s) :
    res = [hashid for hashid in TARGET_DB if TARGET_DB[hashid][1] == _size]

    if not res:
        return (True,
                hashfile64(filename=filename,
                           stop_after=CST__PARTIALHASHID_BYTESNBR),
                hashfile64(filename=filename))

    # (2) how many file(s) among those in <res> have a partial hashid equal
    # to the partial hashid of filename ?
    src_partialhashid = hashfile64(filename=filename,
                                   stop_after=CST__PARTIALHASHID_BYTESNBR)

    new_res = [hashid for hashid in res if TARGET_DB[0] == target_partialhashid]

    res = new_res
    if not res:
        return (True,
                src_partialhashid,
                hashfile64(filename=filename))

    # (3) how many file(s) among those in <res> have an hashid equal to the
    # hashid of filename ?
    src_hashid = hashfile64(filename=filename)
    new_res = [hashid for hashid in res if hashid == src_hashid]

    res = new_res
    if not res:
        return (True,
                src_partialhashid,
                src_hashid)

    if not ARGS.strictcmp:
        return (False, None, None)

    # (4) bit-to-bit comparision :
    for hashid in res:
        if not filecmp.cmp(filename, TARGET_DB[hashid][2], shallow=False):
            return (True,
                    src_partialhashid,
                    src_hashid)

    return (False, None, None)

#///////////////////////////////////////////////////////////////////////////////
def thefilehastobeadded__db2(filename, _size):
    """
        thefilehastobeadded__db()
        ________________________________________________________________________

        Return True if the file isn't already known in the database.
        ________________________________________________________________________

        PARAMETERS
                o filename     : (str) file's name
                o _size         : (int) file's size, in bytes.

        About the underscore before "_size" :
        confer https://www.python.org/dev/peps/pep-0008/#function-and-method-arguments
          " If a function argument's name clashes with a reserved keyword, it is generally
          " better to append a single trailing underscore rather than use an abbreviation
          " or spelling corruption.

        RETURNED VALUE
                either (False, None, None)
                either (True, partial hashid, hashid)
    """
    # (1) how many file(s) in the database have a size equal to _size ?
    # a list of hashid(s) :
    res = [hashid for hashid in TARGET_DB if TARGET_DB[hashid][1] == element.size]

    if not res:
        return True

    # (2) how many file(s) among those in <res> have a partial hashid equal
    # to the partial hashid of filename ?
    new_res = [hashid for hashid in res if TARGET_DB[hashid][0] == element.partialhashid]

    res = new_res
    if not res:
        return True

    # (3) how many file(s) among those in <res> have an hashid equal to the
    # hashid of filename ?
    new_res = [hashid for hashid in res if hashid == element.hashid]

    res = new_res
    if not res:
        return True

    if ARGS.strictcmp:
        # (4) bit-to-bit comparision :
        return all(not filecmp.cmp(element.filename, TARGET_DB[hashid][2], shallow=False)
                   for hashid in res)

    # else, if some files stay, they must be equal
    return False

#///////////////////////////////////////////////////////////////////////////////
def welcome(timestamp_start):
    """
        welcome()
        ________________________________________________________________________

        Display a welcome message with some very broad informations about the
        program. This function may be called before reading the configuration
        file (confer the variable CFG_PARAMETERS).

        This function is called before the opening of the log file; hence, all
        the messages are only displayed on console (see the welcome_in_logfile()
        function)
        ________________________________________________________________________

        PARAMETER :
                o  timestamp_start : a datetime.datetime object

        no RETURNED VALUE

        sys.exit(-1) if the config file doesn't exist.
    """
    # first welcome message :
    strmsg = ("=== {0} v.{1} "
              "(launched at {2}) ===").format(__projectname__,
                                              __version__,
                                              timestamp_start.strftime("%Y-%m-%d %H:%M:%S"))
    print("="*len(strmsg))
    print(strmsg)
    print("="*len(strmsg))

    # command line arguments :
    print("  = command line arguments : ", sys.argv)

    # if the target file doesn't exist, it will be created later by main_warmup() :
    if ARGS.new is None and ARGS.downloaddefaultcfg is None:
        print("  = target directory given as parameter : \"{0}\" "
              "(path : \"{1}\")".format(ARGS.targetpath, normpath(ARGS.targetpath)))

        if ARGS.configfile is not None:
            print("  = expected config file : \"{0}\" "
                  "(path : \"{1}\")".format(ARGS.configfile, normpath(ARGS.configfile)))
        else:
            print("  * no config file specified on the command line : "
                  "let's search a config file...")

    if ARGS.off:
        print("  = --off option detected :")
        print("  =                no file will be modified, no directory will be created")
        print("  =                but the corresponding messages will be written in the")
        print("  =                log file.")

#///////////////////////////////////////////////////////////////////////////////
def welcome_in_logfile(timestamp_start):
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
                o  timestamp_start : a datetime.datetime object

        no RETURNED VALUE
    """
    FILE_LOGGER.info("=== %s v.%s " "(launched at %s) ===",
                     __projectname__, __version__, timestamp_start.strftime("%Y-%m-%d %H:%M:%S"))

    FILE_LOGGER.info("  = command line arguments : %s", sys.argv)

    FILE_LOGGER.info("  = target directory given as parameter : \"%s\" "
                     "(path : \"%s\")", ARGS.targetpath,
                     normpath(ARGS.targetpath))

#///////////////////////////////////////////////////////////////////////////////

#///////////////////////////////////////////////////////////////////////////////
#/////////////////////////////// STARTING POINT ////////////////////////////////
#///////////////////////////////////////////////////////////////////////////////
if __name__ == '__main__':
    main()

