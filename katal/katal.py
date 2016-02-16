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
import hashlib
from datetime import datetime
import filecmp
from fnmatch import fnmatch
import logging
from logging.handlers import RotatingFileHandler
import operator
import os
import platform
import re
import shutil
import sqlite3
import subprocess
import urllib.request
import sys


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


try:
    from xdg.BaseDirectory import load_first_config
except ImportError:
    XDG_CONFIG = ''
else:
    XDG_CONFIG = load_first_config(__projectname__)

#===============================================================================
# loggers
#===============================================================================
def extra_logger(custom_parameters):
    """"
        extraLogger(custom_parameters)
        ________________________________________________________________________

        Mainly for syntax sugar.

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
                       'db_index INTEGER PRIMARY KEY,'
                       'hashid TEXT , '
                       'partialhashid TEXT, '
                       'size INTEGER, '
                       'targetname TEXT UNIQUE, '
                       'sourcename TEXT, '
                       'time INTEGER, '
                       'tagsstr TEXT)')

CST__TAG_SEPARATOR = ";"  # symbol used in the database between two tags.

CST__TASKS_SUBSUBDIR = "tasks"

CST__TRASH_SUBSUBDIR = "trash"

# 'Linux', 'Windows', 'Java' according to https://docs.python.org/3.5/library/platform.html
CST__PLATFORM = platform.system()

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

    def read_config(self, args=None, cfg_file=None):
        """
        self.read_config(self, args=None, cfg_file=None)
        ________________________________________________________________________

        Read all the config from the different sources (default values, default
        config files, command line, cfg_file if provided)
        """

        self.read_command_line_arguments(args)

        # TODO: download configfile
        self.read_dict(self.default_config())    # Initialize the defaults value
        self.read_all_config_files(cfg_file)
        self.read_dict(self.arguments_to_dict()) # Modifications from command line

        self.read_parameters_from_cfgfile()

    def arguments_to_dict(self):
        """
        self.arguments_to_dict() -> dict

        ________________________________________________________________________

        Convert the argument to a dict ready to be parsed by self.read_dict to
        update config.
        """
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
    @staticmethod
    def default_config():
        """self.default_config() -> dict of default config"""
        return {
            'source': {
                'path': '.',
                'eval': '*',
                'strict comparison': False,
                'read hidden files': False,
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

    @property
    def normtargetpath(self):
        """self.normtargetpath -> normpath(self.targetpath)"""
        return normpath(self.targetpath)

    def read_all_config_files(self, cfg_file=None):
        """
        self.read_all_config_files()

        ________________________________________________________________________

        Read all default config files from self.possible_paths_to_cfg(), read
        the config file passed as an argument, and cfg_file if provided.
        """
        # Order matter
        config_files = self.possible_paths_to_cfg()

        cfg_files = self.read(config_files)

        if self.configfile:
            try:
                with open(self.configfile) as file:
                    self.read_file(file)
                    cfg_files.append(self.configfile)
            except FileNotFoundError:
                print('  ! The config file "%s" (path : "%s") '
                      " doesn't exist. " % self.configfile, normpath(self.configfile))
                raise ConfigError

        if cfg_file:
            cfg_files.append(self.read(cfg_file))

        if not cfg_files:
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
                            "'normal'=messages to the console and questions asked on the console; "
                            "'high'=display discarded files. A question may be asked only by "
                            "using the following arguments : --new, --rebase, --reset and --select")

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
    @staticmethod
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

        res.append(os.path.join(normpath("~"), ".katal"))
        if XDG_CONFIG:
            res.append(XDG_CONFIG)

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

            Read the configfile and return the parser. If an error occurred, a
            ConfigError is raised.

            If the mode is set to 'nocopy', parser["target"]["name of the target files"]
            is set to "%i" .
            ________________________________________________________________________

            NO PARAMETER

            RETURNED VALUE
                    self
            EXCEPTION
                    A ConfigError if an error occurred while reading the configuration file

        """
        global USE_LOGFILE

        parser = self
        try:
            USE_LOGFILE = parser["log file"].getboolean("use log file")
            # just to check the existence of the following values in the configuration file :
            assert "maximal size" in parser["log file"]
            assert "name" in parser["log file"]
            assert "name of the target files" in parser["target"]
            assert "mode"in parser["target"]
            assert "eval"in parser["source"]
            assert "path"in parser["source"]
            assert "target filename.max length on console" in parser["display"]
            assert "hashid.max length on console" in parser["display"]
            assert "tag.max length on console" in parser["display"]
            assert "source filename.max length on console" in parser["display"]
        except (KeyError, AssertionError) as exception:
            print("  ! An error occurred while reading config files.")
            print('  ! Your configuration file lacks a specific value : "%s".' % exception)
            print("  ... you should download a new default config file : "
                  "see -dlcfg/--downloaddefaultcfg option")
            raise ConfigError
        except configparser.Error as exception:
            print("  ! An error occurred while reading the config files.")
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
        self.conditions['external program'] = \
            self.match_external(config.get('external program'))

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
                filter_date = filter_date[(len(condition)):].strip()
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
                filter_date = datetime.strptime(filter_date, time_format).timestamp()
                break
            except ValueError:
                pass
        else:
            raise KatalError("Can't analyse the 'date' field {}, see "
                             "configuration example for correct format".format(filter_date))


        def return_match(name):
            # protection against the FileNotFoundError exception.
            # This exception would be raised on broken symbolic link o
            if not os.path.exists(name):
                return False

            # do not use utcfromtimestamp ; since time_format is given in local
            # tz, time must be also in local tz.
            time = os.stat(name).st_mtime
            return op(time, filter_date)

        return return_match

    def match_regex(self, regex):
        """
        self.match_regex(regex) -> test_function
        ________________________________________________________________________

        Analyze the parameter filter_regex and return a function which test if
        the basename of the file match the regex.
        ________________________________________________________________________

        PARAMETERS
                o regex : (str) the string from config file corresponding
                                to the condition on date (eg. .*\\.jpg).

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

    def match_external(self, filter_external):
        """
        self.match_external(filter_external) -> test_function
        ________________________________________________________________________

        Return a funcion which run filter_external as a command with '%s'
        substitued by the file name. If the return code of the command is 0, the
        file is accepted.
        ________________________________________________________________________

        PARAMETERS
                o filter_external : (str) a command

        RETURNED VALUE
                o function(file_name) : function which test if the file succeed
                                        the test run by filter_external
                                        If the return code is 0, return True,
                                        else return False
        """
        if not filter_external:
            return lambda name: True

        if '%s' not in filter_external:
            filter_external += ' %s'

        def return_match(name):
            command = filter_external % name
            out = subprocess.run(command.split(), timeout=True)
            LOGGER.error(command)
            LOGGER.error(out.returncode)
            return not out.returncode

        return return_match

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
            LOGGER.info('  o The following tests failed for filter "%s" and file "%s": '
                        '%s', self.name, file_name, list_tests_failled)
            return False
        else:
            return True

    def __call__(self, file_set):
        """
        self(file_set) -> set(file_name in file_set if self.test(file_name))
        """
        return {file_name for file_name in file_set if self.test(file_name)}

    def __and__(self, filter2):
        """
        Return (self & filter2)

        (self & filter2)(file_name) <=> self(file_name) and filter2(file_name)
        """
        return lambda file_set: self(file_set) & filter2(file_set)

    def __or__(self, filter2):
        """
        Return (self | filter2)

        (self | filter2)(file_name) <=> self(file_name) or² filter2(file_name)
        """
        return lambda file_set: self(file_set) | filter2(file_set)

    def __xor__(self, filter2):
        """
        Return (self ^ filter2)

        (self ^ filter2)(file_name) <=> self(file_name) xor filter2(file_name)
        """
        return lambda file_set: self(file_set) ^ filter2(file_set)

    def __invert__(self):
        """
        Return ~self (not self)

        (~ self)(file_name) <=> not self(file_name)
        """
        return lambda file_set: file_set - self(file_set)

#///////////////////////////////////////////////////////////////////////////////


# The order matter !
# It should be exactly the same than the order of column in database
SelectTuple = namedtuple('SELECTELEMENT', ["db_index",
                                           "hashid",
                                           "partialhashid",
                                           "size",
                                           "targetname",
                                           "srcname",
                                           "time",
                                           "targettags",])
class SelectElement(SelectTuple):
    """
    ATTRIBUTES
        o db_index      : (int) number of the element in db
        o hashid        : (str) hashid of the file
        o partialhashid : (str) partial hashid of the file
        o size          : (int) size in bytes of the file
        o targetname    : (str) full target name of the file, ready to be used by os.path
        o srcname       : (str) full source name of the file, ready to be used by os.path
        o time          : (int) timestamp of last modification of the file
        o targettags    : (str) list of tags


    """
    def __new__(cls, fullname, config=None, srcpath=None, targetpath=None):
        fullname = normpath(fullname)

        data = {}
        data['srcname'] = fullname
        data['size'] = os.stat(fullname).st_size
        data['time'] = os.stat(fullname).st_mtime

        data['db_index'] = cls.get_increase_db_index()

        data['partialhashid'] = hashfile64(filename=fullname,
                                           stop_after=CST__PARTIALHASHID_BYTESNBR)
        data['hashid'] = hashfile64(filename=fullname)

        if targetpath is None:
            targetpath = CONFIG.normtargetpath

        data['targetpath'] = targetpath
        data['srcpath'] = srcpath if srcpath is not None else normpath(CONFIG["source"]["path"])

        data['targetname'] = os.path.join(targetpath, cls.create_target_name(data, config))
        data['targettags'] = cls.create_target_tags(data, config)

        return super().__new__(cls, **{k: v for k, v in data.items() if k in cls._fields})

    @classmethod
    def get_increase_db_index(cls):
        """
        cls.get_increase_db_index() -> db_index
        """
        if not hasattr(cls, '_db_index'):
            con = sqlite3.Connection(get_database_fullname())
            c = con.execute('SELECT COUNT(*) FROM dbfiles')
            db_index = int(c.fetchone()[0])
            con.close()

            cls._db_index = db_index

        cls._db_index += 1
        return cls._db_index

    @classmethod
    def from_db_row(cls, db_row):
        """
        SelectElement.from_db_row(db_row) -> SelectElement
        _______________________________________________________________________

        Create a SelectElement from a row of the database
        _______________________________________________________________________

        PARAMETERS
                o db_row (Row): a row of the database

        RETURNED VALUE
                o the SelectElement corresponding
        """
        data = {}
        data['srcname'] = db_row['sourcename']
        data['size'] = db_row['size']
        data['db_index'] = db_row['db_index']

        data['time'] = db_row['time']

        data['partialhashid'] = db_row['partialhashid']
        data['hashid'] = db_row['hashid']

        data['targetname'] = db_row['targetname']
        data['targettags'] = db_row['tagsstr']

        return super().__new__(cls, **data)

    @classmethod
    def create_target_name(cls, data, config=None):
        """
            Selectelement.create_target_name(data)
            ________________________________________________________________________

            Create the name of a file (a target file) from various informations
            given by the parameter. The function reads the string stored in
            parameters["target"]["name of the target files"] and replaces some
            keywords in the string by the parameters given to this function.

            see the available keywords in the documentation.
                (see documentation:configuration file)
            ________________________________________________________________________

            PARAMETERS
                    o data : (dict) must contain the following items
                        o hashid                       : (str)
                        o srcname                      : (str)
                        o time                         : (int)
                        o size                         : (int)
                        o db_index                     : (int)

            RETURNED VALUE
                    (str)name
        """
        if config is None:
            config = CONFIG
        return cls.add_keywords_in_targetstr(config["target"]["name of the target files"], data)

    #/////////////////////////////////////////////////////////////////////////////////////////
    @classmethod
    def create_target_tags(cls, data, config=None):
        """
            SelectElement.create_target_tags(data)
            ________________________________________________________________________

            Create the tags of a file (a target file) from various informations
            given by the parameter. The function reads the string stored in
            parameters["target"]["tags"] and replaces some
            keywords in the string by the parameters given to this function.

            see the available keywords in the documentation.
                (see documentation:configuration file)
            ________________________________________________________________________

            PARAMETERS
                    o data : (dict) must contain the following items
                        o hashid                       : (str)
                        o srcname                      : (str)
                        o time                         : (int)
                        o size                         : (int)
                        o db_index                     : (int)

            RETURNED VALUE
                    (str)name
        """
        if config is None:
            config = CONFIG
        return cls.add_keywords_in_targetstr(config["target"]["tags"], data)

    @classmethod
    def add_keywords_in_targetstr(cls, srcstring, data):
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
                    o srcstring                        : (str)
                    o data : (dict) must contain the following items
                        o hashid                       : (str)
                        o srcname                      : (str)
                        o time                         : (int)
                        o size                         : (int)
                        o db_index                     : (int)

            RETURNED VALUE
                    (str)the expected string
        """
        res = srcstring

        # to don't have to compile the regex every time
        date_regex = getattr(cls, 'date_regex',
                             re.compile(r"%d\((.*?)\)")) # Match '%d(format)'
        ddate_regex = getattr(cls, 'ddate_regex',
                              re.compile(r"%dd\((.*?)\)")) # Match '%d(format)'
        cls.date_regex = date_regex
        cls.ddate_regex = ddate_regex

        filename = os.path.relpath(data['srcname'], start=data['srcpath'])
        filename_no_extens, extension = get_filename_and_extension(filename) #TODO Put get_filename... as e method ?
        relative_directory = os.path.dirname(filename)

        date = datetime.fromtimestamp(data['time'])

        def date_sub(match):
            return date.strftime(match.group(1))
        def ddate_sub(match):
            return remove_illegal_characters(date.strftime(match.group(1)))

        # beware : order matters !
        res = date_regex.sub(date_sub, res)
        res = ddate_regex.sub(ddate_sub, res)
        res = res.replace("%Y", date.strftime("%Y"))
        res = res.replace("%m", date.strftime("%m"))
        res = res.replace("%d", date.strftime("%d"))

        res = res.replace("%nn", remove_illegal_characters(filename))
        res = res.replace("%n", filename)

        res = res.replace("%rr", remove_illegal_characters(relative_directory))
        res = res.replace("%r", relative_directory)

        res = res.replace("%ht", hex(int(data['time']))[2:])
        res = res.replace("%h", data['hashid'])

        res = res.replace("%ff", remove_illegal_characters(filename_no_extens))
        res = res.replace("%f", filename_no_extens)

        res = res.replace("%pp", remove_illegal_characters(data['srcname']))
        res = res.replace("%p", data['srcname'])

        res = res.replace("%ee", remove_illegal_characters(extension))
        res = res.replace("%e", extension)

        res = res.replace("%s", str(data['size']))

        res = res.replace("%dd", remove_illegal_characters(date.strftime(CST__DTIME_FORMAT)))

        res = res.replace("%t", str(int(data['time'])))

        res = res.replace("%i", str(data['db_index']))

        return res

    #///////////////////////////////////////////////////////////////////////////////

    @property
    def date(self):
        """self.date -> last modification date formated with CST__DTIME_FORMAT"""
        return datetime.fromtimestamp(self.time).strftime(CST__DTIME_FORMAT)
    def __eq__(self, other):
        """
        self.__eq__(other) -> self == other
        _______________________________________________________________________

        Test if two SelectElement are equal. The comparison is based on hashid,
        and if 'strict comparison' is True, on a bit-to-it comparison
        """
        if self.hashid != other.hashid:
            return False
        elif self.partialhashid != other.partialhashid:
            return False
        else:
            if CONFIG.getboolean('source', 'strict comparison'):
                # We have to do a bit-to-bit comparison

                # Protection if only srcname or targetname exists
                self_filename = self.srcname if os.path.exists(self.srcname) else self.targetname
                other_filename = other.srcname if os.path.exists(other.srcname) else other.targetname
                return filecmp.cmp(self_filename, other_filename, shallow=False)
            else:
                return True

    def __hash__(self):
        return hash(self.hashid)

#===============================================================================
# global variables
#===============================================================================

CFG_PARAMETERS = None  # see documentation:configuration file
                       # parameters read from the configuration file.
                       # see the read_parameters_from_cfgfile() function

CONFIG = Config() # centralize all config (command line + configuration file)
                  # see Config()

ARGS = CONFIG     # parameters given on the command line; initialized by main();

INFOS_ABOUT_SRC_PATH = (None, None, None)  # initialized by show_infos_about_source_path()
                                           # ((int)total_size, (int)files_number, (dict)extensions)

TARGET_DB = set()      # see documentation:database; initialized by read_target_db()

SELECT = set()               # see documentation:selection; initialized by action__select()
SELECT_SIZE_IN_BYTES = 0  # initialized by action__select()
FILTER = None             # see documentation:selection; initialized by read_filters()


def action__add():
    """
        action__add()
        ________________________________________________________________________

        Add the source files described in SELECT/SELECT_SIZE_IN_BYTES to the
        target path.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    db_connection = sqlite3.connect(get_database_fullname())
    db_cursor = db_connection.cursor()

    LOGGER.info("    = let's update the database...")
    try:
        if not ARGS.off:
            # The database is filled first so that in case of exception,
            # nothing is done
            files_to_be_added = (element[:8] for element in SELECT)
            db_cursor.executemany('INSERT INTO dbfiles VALUES (?,?,?,?,?,?,?,?)', files_to_be_added)


        # Then we copy the files
        LOGGER.info("  = copying data =")

        if get_disk_free_space(ARGS.targetpath) < SELECT_SIZE_IN_BYTES * CST__FREESPACE_MARGIN:
            raise KatalError("    ! Not enough space on disk. Stopping the program.")

        len_select = len(SELECT)
        mode = CONFIG["target"]["mode"]
        for index, element in enumerate(SELECT, 1):
            source_filename = element.srcname
            target_name = element.targetname

            if mode == "nocopy":
                # nothing to do
                LOGGER.info("    ... (%s/%s) due to the nocopy mode argument, "
                            '"%s" will be simply added in the target database.',
                            index, len_select, source_filename)

            elif mode == "copy" or mode == "move":
                LOGGER.info('    ... (%s/%s) about to %s "%s" to "%s" .',
                            index, len_select, mode, source_filename, target_name)

                if not ARGS.off:
                    copy(source_filename, target_name)

            else:
                raise KatalError('Mode {} not valid'.format(mode))

    except Exception as exception:
        # An error occurred, we cancel the transaction
        db_connection.rollback()
        # remove all previously copied files
        clean(element.targetname for element in SELECT)
        if isinstance(exception, sqlite3.IntegrityError):
            LOGGER.exception("!!! An error occurred while writing the database : ")
            raise KatalError("An error occurred while writing the database.")

        else:
            LOGGER.exception('An error occurred. Aborting the file transfer')
            raise

    else:
        # Everything OK
        LOGGER.info("    = ... database updated.")
        db_connection.commit()

        if mode == "move":
            # Remove all files from source
            clean(element.srcname for element in SELECT)
    finally:
        db_connection.close()

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

    files_to_be_rmved_from_the_db = []
    for element in read_target_db2():
        if not os.path.exists(element.srcname):
            files_to_be_rmved_from_the_db.append(element)
            LOGGER.info("    o about to remove \"%s\" "
                        "from the database", element.srcname)

    if not files_to_be_rmved_from_the_db:
        LOGGER.info("    * no file to be removed : the database is ok.")
    else:
        db_connection = sqlite3.connect(get_database_fullname())
        db_connection.row_factory = sqlite3.Row
        db_cursor = db_connection.cursor()

        for element in files_to_be_rmved_from_the_db:
            if not ARGS.off:
                LOGGER.info("    o removing \"%s\" record "
                            "from the database", element.targetname)
                db_cursor.execute("DELETE FROM dbfiles WHERE targetname=?", (element.targetname,))
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
        print("  ! An error occurred : {0}\n"
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

        RETURNED VALUE:
            o the list of element which have the tag "tag"
    """
    LOGGER.info("  = searching the files with the tag \"%s\"", tag)

    res = []
    for element in read_target_db2():
        if tag in element.targettags.split(','):

            res.append(element)
            LOGGER.info("    o \"%s\" : \"%s\"",
                        element.targetname, tagsstr_repr(element.targettags))

    len_res = len(res)
    if len_res == 0:
        LOGGER.info("    o no file matches the tag \"%s\" .", tag)
    elif len_res == 1:
        LOGGER.info("    o one file matches the tag \"%s\" .", tag)
    else:
        LOGGER.info("    o %s files match the tag \"%s\" .", len_res, tag)

    # --copyto argument :
    if ARGS.copyto:
        LOGGER.info("    o copying the files into \"%s\" (path: \"%s\")",
                    ARGS.copyto, normpath(ARGS.copyto))

        if not os.path.exists(normpath(ARGS.copyto)):
            LOGGER.info("    * let's create \"%s\" (path: \"%s\"",
                        ARGS.copyto, normpath(ARGS.copyto))
            if not ARGS.off:
                os.mkdir(normpath(ARGS.copyto))

        for i, element in enumerate(res, 1):
            filename = os.path.basename(element.targetname)
            src = os.path.join(normpath(ARGS.targetpath), filename)
            dest = os.path.join(normpath(ARGS.copyto), filename)
            LOGGER.info("    o (%s/%s) copying \"%s\" as \"%s\"...",
                        i, len_res, src, dest)
            if not ARGS.off:
                copy(src, dest)

    return res

#///////////////////////////////////////////////////////////////////////////////
def action__infos():
    """
        action__infos()
        ________________________________________________________________________

        Display informations about the source and the target directory
        ________________________________________________________________________

        no PARAMETER

        RETURNED VALUE
                (int) 0 if ok, -1 if an error occurred
    """
    LOGGER.info("  = informations =", color="white")
    show_infos_about_source_path()
    return show_infos_about_target_path()

#///////////////////////////////////////////////////////////////////////////////
def action__new(targetname):
    """
        action__new()
        ________________________________________________________________________

        Create a new target directory, or fill it if it already exists but is empty.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    LOGGER.info("  = about to create a new target directory "
                "named \"%s\" (path : \"%s\")", targetname, normpath(targetname))

    targetname = normpath(targetname)

    if os.path.isfile(targetname) or \
            (os.path.isdir(targetname) and os.listdir(targetname)):
        LOGGER.warning("  ! can't go further : the directory already exists.")
        raise FileExistsError

    if not ARGS.off:
        LOGGER.info("  ... creating the target directory with its sub-directories...")
        create_empty_db(targetname)

    if ARGS.verbosity != 'none':
        answer = \
            input(("\nDo you want to download the default config file "
                   "into the expected directory ? (y/N) "))

        if answer in ("y", "yes"):
            res = action__downloadefaultcfg(
                os.path.join(targetname, CST__KATALSYS_SUBDIR, CST__DEFAULT_CONFIGFILE_NAME),
                "local")
            if not res:
                LOGGER.warning("  ! A problem occurred : "
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
    newtargetpath = normpath(newtargetpath)
    source_path = CFG_PARAMETERS["source"]["path"]

    LOGGER.info("  = copying the current target directory into a new one.")
    LOGGER.info("    o from %s (path : \"%s\")", source_path, normpath(source_path))
    LOGGER.info("    o to   %s", newtargetpath)

    to_configfile = os.path.join(newtargetpath,
                                 CST__KATALSYS_SUBDIR,
                                 CST__DEFAULT_CONFIGFILE_NAME)
    LOGGER.info("    o trying to read dest config file %s ", to_configfile)

    dest_params = Config()
    dest_params.read_config([], to_configfile)

    if dest_params is None:
        LOGGER.warning("    ! can't read the dest config file !")
        return

    LOGGER.info("    o config file found and read (ok)")
    LOGGER.info("    o new filenames' format : %s",
                dest_params["target"]["name of the target files"])
    LOGGER.info("    o tags to be added : %s",
                dest_params["target"]["tags"])

    new_db = os.path.join(newtargetpath, CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)
    if not ARGS.off:
        if os.path.exists(new_db):
            LOGGER.warning("  ! Removing already existing database at %s", new_db)
            # let's delete the previous new database :
            os.remove(new_db)

    # let's compute the new names :
    files, anomalies_nbr = action__rebase__files(newtargetpath, dest_params)

    go_on = True
    if anomalies_nbr:
        go_on = False
        answer = \
            input(("\nAt least one anomaly detected (see details above) "
                   "Are you sure you want to go on ? (y/N) "))

        if answer in ("y", "yes"):
            go_on = True

    if go_on and not ARGS.off:
        action__rebase__write(new_db, files)

#///////////////////////////////////////////////////////////////////////////////
def action__rebase__files(newtargetpath, dest_params):
    """
        action__rebase__files()
        ________________________________________________________________________

        Return a dict of the files to be copied (old name, new name, ...) and
        the number of anomalies.

        Anomalies : files' names collisions.
        ________________________________________________________________________

        PARAMETER :
                o olddb_cursor         : cursor to the source database
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
    files = set()       # set to be returned.
    filenames = set()   # to be used to avoid duplicates.

    anomalies_nbr = 0
    for old_element in read_target_db2():
        fullname = old_element.targetname

        new_element = SelectElement(fullname, srcpath=CONFIG.normtargetpath,
                                    targetpath=newtargetpath, config=dest_params)
        new_name = new_element.targetname

        LOGGER.info("      o %s : %s would be copied as %s",
                    old_element.hashid, fullname, new_name)

        if new_name in filenames:
            LOGGER.warning("      ! anomaly : ancient file %s should be renamed as %s "
                           "but this name would have been already created "
                           "in the new target directory ! ",
                           fullname, new_name)
            LOGGER.warning("        Two different files from the ancient target directory "
                           "can't bear the same name in the new target directory !")
            anomalies_nbr += 1
        elif os.path.exists(new_name):
            LOGGER.warning("      ! anomaly : ancient file %s should be renamed as %s "
                           "but this name already exists in new target directory !",
                           fullname, new_name,)
            anomalies_nbr += 1
        else:
            files.add(new_element)
            filenames.add(new_name)

    return files, anomalies_nbr

#///////////////////////////////////////////////////////////////////////////////
def action__rebase__write(new_db, files):
    """
        action__rebase__write()
        ________________________________________________________________________

        Write the files described by "files" in the new target directory.
        ________________________________________________________________________

        PARAMETER :
                o new_db                : (str) new database's name
                o files                : (dict) see action__rebase__files()

        no RETURNED VALUE
    """
    # let's write the new database :
    newdb_connection = sqlite3.connect(new_db)
    newdb_cursor = newdb_connection.cursor()

    try:
        for index, futurefile in enumerate(files, 1):

            strdate = datetime.utcfromtimestamp(futurefile.time).strftime(CST__DTIME_FORMAT)
            LOGGER.info("    o (%s/%s) adding a file in the new database", index, len(files))
            LOGGER.info("      o hashid      : %s", futurefile.hashid)
            LOGGER.info("      o source name : \"%s\"", futurefile.srcname)
            LOGGER.info("      o desti. name : \"%s\"", futurefile.targetname)
            LOGGER.info("      o source date : %s", strdate)
            LOGGER.info("      o size        : %s", size_as_str(futurefile.size))
            LOGGER.info("      o tags        : \"%s\"", futurefile.targettags)

            if not ARGS.off:
                newdb_cursor.execute('INSERT INTO dbfiles VALUES (?,?,?,?,?,?,?,?)', futurefile[:8])


        # let's copy the files :
        for index, futurefile in enumerate(files, 1):
            old_name, new_name = futurefile.srcname, futurefile.targetname

            LOGGER.info("    o (%s/%s) copying \"%s\" as \"%s\"",
                        index, len(files), old_name, new_name)
            if not ARGS.off:
                copy(old_name, new_name)

    except sqlite3.IntegrityError as exception:
        newdb_connection.rollback()
        clean(file.targetname for file in files)
        LOGGER.exception("!!! An error occurred while writing the new database : ")
        raise KatalError("An error occurred while writing the new database : " + str(exception))

    except Exception:
        newdb_connection.rollback()
        clean(file.targetname for file in files)
        LOGGER.exception("!!! An error occurred while copying the files : ")
        raise

    else:
        newdb_connection.commit()
    finally:
        newdb_connection.close()
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

    if ARGS.verbosity != 'none':
        answer = \
            input(("\nDo you really want to delete (=move to the katal trash directory)"
                   "the files in the target directory and the database (y/N) "))
        if answer not in ("y", "yes"):
            return

    # a list of fullname
    files_to_be_removed = [element.targetname for element in read_target_db2()]

    db_connection = sqlite3.connect(get_database_fullname())
    db_cursor = db_connection.cursor()

    for name in files_to_be_removed:
        LOGGER.info("   o removing %s from the database and from the target path", name)
        if not ARGS.off:
            # let's remove the file from the target directory :
            shutil.move(name,
                        os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR,
                                     os.path.basename(name)))
            # let's remove the file from the database :
            db_cursor.execute("DELETE FROM dbfiles WHERE targetname=?", (name,))

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

    files_to_be_removed = [element.targetname for element in read_target_db2()
                           if not element.targettags]    # list of name

    target_trash = [os.path.join(normpath(ARGS.targetpath), CST__KATALSYS_SUBDIR,
                                 CST__TRASH_SUBSUBDIR, os.path.basename(name))
                    for name in files_to_be_removed]

    if not files_to_be_removed:
        LOGGER.warning("   ! no files to be removed.")
    else:
        try:
            db_connection = sqlite3.connect(get_database_fullname())
            db_cursor = db_connection.cursor()

            for name, target in zip(files_to_be_removed, target_trash):
                LOGGER.info("   o removing %s from the database and from the target path", name)
                if not ARGS.off:
                    # let's remove the file from the target directory :
                    copy(name, target)

                    # let's remove the file from the database :
                    db_cursor.execute("DELETE FROM dbfiles WHERE targetname=?", (name,))

        except Exception:
            LOGGER.exception("  ! An error occurred. Reverting to previous state")
            db_connection.rollback()
            clean(target_trash)
            raise
        else:
            db_connection.commit()
            clean(files_to_be_removed)
        finally:
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

    if not SELECT:
        LOGGER.warning("    ! no file selected ! "
                       "You have to modify the config file to get some files selected.")
    else:
        ratio = len(SELECT) / (len(SELECT) + number_of_discarded_files) * 100.0
        LOGGER.info("    o number of selected files "
                    "(after discarding %s file(s)) : %s, "
                    "%.2f%% of the source files.",
                    len(SELECT), number_of_discarded_files, ratio)

    # let's check that the target path has sufficient free space :
    if CFG_PARAMETERS["target"]["mode"] != "nocopy":
        available_space = get_disk_free_space(ARGS.targetpath)
        if available_space > SELECT_SIZE_IN_BYTES * CST__FREESPACE_MARGIN:
            LOGGER.info("    o required space : %s; "
                        "available space on disk : %s (ok)",
                        size_as_str(SELECT_SIZE_IN_BYTES), size_as_str(available_space),)
        else:
            LOGGER.error("    o required space : %s; "
                         "available space on disk : %s (!!! problem !!!)",
                         size_as_str(SELECT_SIZE_IN_BYTES), size_as_str(available_space),)

    # if there's no --add option, let's give some examples of the target names :
    if not ARGS.add and CFG_PARAMETERS["target"]["mode"] != "nocopy":
        for i, element in enumerate(SELECT):
            LOGGER.info("    o e.g. ... \"%s\" "
                        "would be copied as \"%s\" .", element.srcname, element.targetname)

            if i >= 5:
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

    if not os.path.exists(get_database_fullname()):
        LOGGER.warning("    ! no database found.")
        return -3
    else:
        # We test if filename is already in db
        for element in read_target_db2():
            if element.name == os.path.join(normpath(ARGS.targetpath), filename):
                break
        else:
            LOGGER.warning("    ! can't find \"%s\" file in the database.", filename)
            return -2

        if not ARGS.off:
            db_connection = sqlite3.connect(get_database_fullname())
            db_cursor = db_connection.cursor()

            # let's remove filename from the target directory :
            shutil.move(os.path.join(normpath(ARGS.targetpath), filename),
                        os.path.join(normpath(ARGS.targetpath),
                                     CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR, filename))

            # let's remove filename from the database :
            db_cursor.execute("DELETE FROM dbfiles WHERE targetname=?", (filename,))

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
        """Display the expected informations about a file named srcfile_name."""

        LOGGER.info("  = what about the \"%s\" file ? (path : \"%s\")", src, srcfile_name)
        element = SelectElement(srcfile_name)
        LOGGER.info("    = size : %s", size_as_str(element.size))
        LOGGER.info("    = mtime : %s (epoch value : %s)", element.date, element.time)
        LOGGER.info("    = hash : %s", element.hashid)

        # is the hash in the database ?
        if element in TARGET_DB:
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

        for dirpath, _, filenames in walk_hidden(normsrc):
            for filename in filenames:
                fullname = os.path.join(normpath(dirpath), filename)
                show_infos_about_a_srcfile(fullname)

    else:
        # informations about the source file :
        if normpath(ARGS.targetpath) not in normsrc:
            # normal case : the file is outside the target directory :
            show_infos_about_a_srcfile(normsrc)

        else:
            # special case : the file is inside the target directory :
            LOGGER.info("  = what about the \"%s\" file ? (path : \"%s\")", src, normsrc)
            LOGGER.info("    This file is inside the target directory.")
            LOGGER.info("    Informations extracted from the database :")
            # informations from the database :
            db_connection = sqlite3.connect(get_database_fullname())
            db_connection.row_factory = sqlite3.Row
            db_cursor = db_connection.cursor()
            for db_record in db_cursor.execute("SELECT * FROM dbfiles WHERE targetname=?", (src,)):
                LOGGER.info("    = hash : %s", db_record["hashid"])
                LOGGER.info("    = partial hashid : %s", db_record["partialhashid"])
                LOGGER.info("    = name : %s", db_record["targetname"])
                LOGGER.info("    = size : %s", db_record["size"])
                LOGGER.info("    = source name : %s", db_record["sourcename"])
                LOGGER.info("    = source date : %s", db_record["sourcedate"])
                LOGGER.info("    = tags' string : %s", db_record["tagsstr"])
            db_connection.close()

    return True

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
def clean(list_path):
    """
    clean(list_path)
    ___________________________________________________________________________

    Clean all given paths : remove each path if it exists, else do nothing.
    ___________________________________________________________________________

    PARAMETERS :
            o list_path : (iterable) all the paths to clean

    NO RETURNED VALUE
    """
    if not ARGS.off:
        for path in list_path:
            if os.path.isfile(path):
                os.remove(path)

def copy(src, dst):
    """
    copy(src, dst)
    ___________________________________________________________________________

    Copy file from src to dst and create parent directory if needed
    """
    try:
        shutil.copy2(src, dst)
    except FileNotFoundError:
        if not os.path.exists(os.path.dirname(dst)):
            os.makedirs(os.path.dirname(dst))
            shutil.copy2(src, dst)
        else:
            # The exception has been raised for something else
            raise
def create_empty_db(targetpath=None):
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
    if targetpath is None:
        targetpath = normpath(ARGS.targetpath)
    db_name = os.path.join(targetpath, CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)

    LOGGER.info("  ... creating an empty database named \"%s\"...", db_name)


    if not ARGS.off:
        if not os.path.isdir(os.path.dirname(db_name)):
            create_subdirs_in_target_path(targetpath)

        db_connection = sqlite3.connect(db_name)
        db_cursor = db_connection.cursor()

        db_cursor.execute(CST__SQL__CREATE_DB)

        db_connection.commit()
        db_connection.close()

    LOGGER.info("   ... database created")

#///////////////////////////////////////////////////////////////////////////////
def create_subdirs_in_target_path(targetpath=None):
    """
        create_subdirs_in_target_path()
        ________________________________________________________________________

        Create the expected subdirectories in ARGS.targetpath .

        No log messages for this function, everything is printed to the console.
        ________________________________________________________________________

        no PARAMETERS, no RETURNED VALUE
    """
    if targetpath is None:
        targetpath = normpath(ARGS.targetpath)
    # (str)name for the message, (str)full path :
    for name, fullpath in \
            (("target", targetpath),
             ("system", os.path.join(targetpath,
                                     CST__KATALSYS_SUBDIR)),
             ("trash", os.path.join(targetpath,
                                    CST__KATALSYS_SUBDIR, CST__TRASH_SUBSUBDIR)),
             ("log", os.path.join(targetpath,
                                  CST__KATALSYS_SUBDIR, CST__LOG_SUBSUBDIR)),
             ("tasks", os.path.join(targetpath,
                                    CST__KATALSYS_SUBDIR, CST__TASKS_SUBSUBDIR))):
        if not os.path.exists(fullpath) and not ARGS.off:
            LOGGER.info('  * Since the %s path "%s" '
                        "doesn't exist, let's create it.", name, fullpath)
            os.mkdir(fullpath)

#/////////////////////////////////////////////////////////////////////////////////////////
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
def fill_select():
    """
        fill_select()
        ________________________________________________________________________

        Fill SELECT and SELECT_SIZE_IN_BYTES from the files stored in
        the source path. This function is used by action__select() .
        ________________________________________________________________________

        no PARAMETERS

        RETURNED VALUE
                (int) the number of discarded files
    """
    global SELECT_SIZE_IN_BYTES, SELECT

    def prefix(index):
        # if we know the total amount of files to be selected (see the --infos option),
        # we can add the percentage done :
        if INFOS_ABOUT_SRC_PATH[1]:
            return "[{0:.4f}%] ".format(index / INFOS_ABOUT_SRC_PATH[1] * 100.0)
        else:
            return ""

    index = 0

    source_path = normpath(CFG_PARAMETERS["source"]["path"])

    # (1) find all source files
    name_set = {os.path.join(dirpath, filename)
                for dirpath, _, filenames in walk_hidden(source_path)
                for filename in filenames}

    # (2) Check all source files really defined
    # protection against the FileNotFoundError exception.
    # This exception would be raised on broken symbolic link
    file_not_existing = {filename for filename in name_set if not os.path.exists(filename)}
    for filename in file_not_existing:
        index += 1
        LOGGER.warning("    ! %sbrowsing %s, an error occurred : "
                       "can't read the file \"%s\"", prefix(index), source_path, filename)

    name_set.difference_update(file_not_existing)

    # (3) Filter files
    filtered_files = FILTER(name_set)
    for filename in name_set - filtered_files:
        # nothing : incompatibility with at least one filter :
        index += 1
        LOGGER.debug("    - %sdiscarded \"%s\" : incompatibility with the filter(s)",
                     prefix(index), filename)

    # (4) Transform the file in an element object
    filtered_elements = {SelectElement(filename) for filename in filtered_files}

    # (5) Check element not already definided in TARGET_DB
    for element in filtered_elements & TARGET_DB:
        index += 1
        # element already defined in db : let's discard <filename> :
        LOGGER.debug("    - %s(similar hashid in the database) "
                     "discarded \"%s\"", prefix(index), element.targetname)

    filtered_elements.difference_update(TARGET_DB)

    # (6) Check target name not already existing
    name_already_exists = {element for element in filtered_elements
                           if os.path.exists(element.targetname)}
    if name_already_exists:
        for element in name_already_exists:
            LOGGER.error('    ! Two files saved as target "%s". Aborting',
                         element.targetname)
        raise KatalError('Find targetnames which will be unique')

    # (7) Check no targetname used twice
    dest_names = set()
    abort = False
    for element in filtered_elements:
        if element.targetname in dest_names:
            LOGGER.error('    ! Name "%s" used by "%s" already existing. Aborting',
                         element.targetname, element.srcname)
            abort = True
        else:
            dest_names.add(element.targetname)
    if abort:
        raise KatalError('Find targetnames which will be unique')

    # (8)ok, let's add <filename> to SELECT...
    for element in filtered_elements:
        index += 1
        LOGGER.info("    + %s selected \"%s\", size=%s; date=%s",
                    prefix(index), element.targetname, element.size, element.date)

    SELECT = filtered_elements

    SELECT_SIZE_IN_BYTES = sum(element.size for element in SELECT)
    number_of_discarded_files = len(name_set) - len(SELECT)

    return number_of_discarded_files

#///////////////////////////////////////////////////////////////////////////////
def get_database_fullname(targetpath=None):
    """
        get_database_fullname()
        ________________________________________________________________________

          Return the full name (=full path + name) of the database in
        ARGS.targetpath. If the database does not exist, create it.
        ________________________________________________________________________

        NO PARAMETER

        RETURNED VALUE
                the expected string
    """
    if targetpath is None:
        targetpath = normpath(ARGS.targetpath)
    db_fullname = os.path.join(targetpath, CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)

    if not os.path.exists(db_fullname):
        create_empty_db(targetpath)

    return db_fullname

#///////////////////////////////////////////////////////////////////////////////
def get_disk_free_space(path):
    """
        get_disk_free_space()
        ________________________________________________________________________

        return the available space on disk() in bytes.
        ________________________________________________________________________

        PARAMETER
                o path : (str) the source path belonging to the disk to be
                          analysed.

        RETURNED VALUE
                the expected int(eger)
    """
    # Normally, whutil should be plateform independant.
    return shutil.disk_usage(normpath(path)).free

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
    fname_no_extens, extension = os.path.splitext(os.path.basename(path))

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
    global ARGS

    timestamp_start = datetime.now()

    try:
        ARGS = CONFIG.read_command_line_arguments(args)

        main_warmup(timestamp_start)
        main_actions_tags()
        main_actions()

        goodbye(timestamp_start)

    except KatalError as exception:
        if LOGGER:
            LOGGER.exception("(%s) ! a critical error occurred.\n"
                             "Error message : %s", __projectname__, exception)
        else:
            print("({0}) ! a critical error occurred.\n"
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

        if ARGS.verbosity != 'none' and SELECT:
            answer = \
                input("\nDo you want to update the target database and to {0} the selected "
                      "files into the target directory "
                      "(\"{1}\") ? (y/N) ".format(CFG_PARAMETERS["target"]["mode"],
                                                  ARGS.targetpath))

            if answer in ("y", "yes", "Y"):
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
    for path, info in ((os.path.join(normpath(ARGS.targetpath),
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

        files_to_be_modified = [element for element in read_target_db2()
                                if fnmatch(element.name, dest)]       # a list of name

        if not files_to_be_modified:
            LOGGER.info("    * no files match the given name(s) given as a parameter.")
        else:
            db_connection = sqlite3.connect(get_database_fullname())
            db_cursor = db_connection.cursor()

            # let's apply the tag(s) to the <files_to_be_modified> :
            for element in files_to_be_modified:

                LOGGER.info("    o applying the tag string \"%s\" to %s.", tag, element.targetname)

                if ARGS.off:
                    pass

                elif mode == "set":
                    sqlorder = 'UPDATE dbfiles SET tagsstr=? WHERE targetname=?'
                    db_cursor.execute(sqlorder, (tag, element.targetname))

                elif mode == "append":
                    sqlorder = ('UPDATE dbfiles SET tagsstr=? WHERE targetname=?')
                    db_cursor.execute(sqlorder, (element.targettags + CST__TAG_SEPARATOR + tag,
                                                 element.targetname))

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
    res = os.path.normpath(os.path.abspath(os.path.expanduser(str(path))))

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
def read_target_db(database=None):
    """
        read_target_db()
        ________________________________________________________________________

        Read the database stored in the target directory and initialize
        TARGET_DB.
        ________________________________________________________________________

        no PARAMETER, no RETURNED VALUE
    """
    if database is None:
        database = get_database_fullname()

    db_connection = sqlite3.connect(database)
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        TARGET_DB.add(SelectElement.from_db_row(db_record))

    db_connection.close()

#/////////////////////////////////////////////////////////////////////////////////////////
def read_target_db2(database=None):
    """
        read_target_db()
        ________________________________________________________________________

        Read the database stored in the target directory and returned a set of
        SelectElement from the database.
        ________________________________________________________________________

        no PARAMETER,

        RETURNED VALUE
                o target_db : (set) SelectElement objects corresponding to the
                rows of the database
    """
    if database is None:
        database = get_database_fullname()

    db_connection = sqlite3.connect(database)
    db_connection.row_factory = sqlite3.Row
    db_cursor = db_connection.cursor()

    target_db = set()
    for db_record in db_cursor.execute('SELECT * FROM dbfiles'):
        target_db.add(SelectElement.from_db_row(db_record))

    db_connection.close()

    return target_db

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
    for char in ("*", "/", "\\", ".", "[", "]", ":", ";", "|", "=", ",", "?", "<", ">", "-", " "):
        src = src.replace(char, "_")
    return src

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
        return "[...]"+string[- (max_length-5):]
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
    for dirpath, _, fnames in walk_hidden(normpath(source_path)):
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
                LOGGER.warning("    ! browsing %s, an error occurred : "
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

        no PARAMETER, no RETURNED VALUE
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
        raise FileNotFoundError("Can't find target path \"%s\"." % ARGS.targetpath)

    if not os.path.isdir(normpath(ARGS.targetpath)):
        raise NotADirectoryError("target path \"%s\" isn't a directory." % ARGS.targetpath)

    if not os.path.exists(os.path.join(normpath(ARGS.targetpath),
                                       CST__KATALSYS_SUBDIR, CST__DATABASE_NAME)):
        LOGGER.warning("    o no database in the target directory.")

    #...........................................................................
    rows_data = []
    row_index = 0
    for element in read_target_db2():
        sourcedate = datetime.fromtimestamp(element.time).strftime(CST__DTIME_FORMAT)

        if CFG_PARAMETERS["target"]["mode"] != 'nocopy':
            rows_data.append((element.hashid,
                              element.targetname,
                              tagsstr_repr(element.tagsstr),
                              element.srcname,
                              sourcedate))
        else:
            rows_data.append((element.hashid,
                              tagsstr_repr(element.tagsstr),
                              element.srcname,
                              sourcedate))
        row_index += 1

    if not row_index:
        LOGGER.warning("    ! (empty database)")
        return

    LOGGER.info("    o %s file(s) in the database :", row_index)

    targetname_maxlength = \
            CFG_PARAMETERS.getint("display", "target filename.max length on console")
    hashid_maxlength = \
            CFG_PARAMETERS.getint("display", "hashid.max length on console")
    tagsstr_maxlength = \
            CFG_PARAMETERS.getint("display", "tag.max length on console")
    sourcename_maxlength = \
            CFG_PARAMETERS.getint("display", "source filename.max length on console")

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
    # Transform ,tag1,tag2, in tag1, tag2
    return ', '.join(s.strip() for s in tagsstr.split(CST__TAG_SEPARATOR) if s)

#///////////////////////////////////////////////////////////////////////////////
def walk_hidden(path):
    """
    walk_hidden(path) -> generator
    ___________________________________________________________________________

    Like os.walk(path), but hide the hidden files if 'read hidden files' is False.
    ___________________________________________________________________________

    PARAMETER
            o path : (str) the path from which to walk

    RETURNED VALUES
            o (dirpath, dirnames, dirfiles) : see os.walk()
    """
    read_hidden = CONFIG.getboolean('source', 'read hidden files')
    for dirpath, dirnames, dirfiles in os.walk(path):
        if read_hidden or not '/.' in dirpath:
            dirnames = [name for name in dirnames
                        if read_hidden or not name.startswith('.')]
            dirfiles = [name for name in dirfiles
                        if read_hidden or not name.startswith('.')]
            yield (dirpath, dirnames, dirfiles)

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

