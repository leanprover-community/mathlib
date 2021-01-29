#!/usr/bin/env python3
"""
Lint a file or files from mathlib for style.

Sample usage:

    $ ./scripts/lint-style.py $(find src archive -name '*.lean')

which will lint all of the Lean files in the specified directories.

The resulting error output will contain one line for each style error
encountered that isn't in the list of allowed / ignored style exceptions.

Paths with no errors will not appear in the output, and the script will
exit with successful return code if there are no errors encountered in
any provided paths.

Paths emitted in the output will match the paths provided on the
command line for any files containing errors -- in particular, linting
a relative path (like ``src/foo/bar.lean``) will produce errors
that contain the relative path, whilst linting absolute paths (like
``/root/mathlib/src/foo/bar.lean``) will produce errors with the
absolute path.

This script can also be used to regenerate the list of allowed / ignored style
exceptions by redirecting the output to ``style-exceptions.txt``:

    $ ./scripts/lint-style.py $(find src archive -name '*.lean') > scripts/style-exceptions.txt
"""

from pathlib import Path
import sys

ERR_COP = 0 # copyright header
ERR_IMP = 1 # import statements
ERR_MOD = 2 # module docstring
ERR_LIN = 3 # line length
ERR_SAV = 4 # ᾰ
ERR_RNT = 5 # reserved notation
ERR_OPT = 6 # set_option

exceptions = []

SCRIPTS_DIR = Path(__file__).parent.resolve()
ROOT_DIR = SCRIPTS_DIR.parent
RESERVED_NOTATION = ROOT_DIR / 'src/tactic/reserved_notation.lean'


with SCRIPTS_DIR.joinpath("style-exceptions.txt").open() as f:
    for line in f:
        filename, _, _, _, _, errno, *_ = line.split()
        path = ROOT_DIR / filename
        if errno == "ERR_COP":
            exceptions += [(ERR_COP, path)]
        if errno == "ERR_IMP":
            exceptions += [(ERR_IMP, path)]
        if errno == "ERR_MOD":
            exceptions += [(ERR_MOD, path)]
        if errno == "ERR_LIN":
            exceptions += [(ERR_LIN, path)]
        if errno == "ERR_SAV":
            exceptions += [(ERR_SAV, path)]
        if errno == "ERR_RNT":
            exceptions += [(ERR_RNT, path)]
        if errno == "ERR_OPT":
            exceptions += [(ERR_OPT, path)]

new_exceptions = False

def skip_comments(enumerate_lines):
    in_comment = False
    for line_nr, line in enumerate_lines:
        if "/-" in line:
            in_comment = True
        if "-/" in line:
            in_comment = False
            continue
        if line == "\n" or in_comment:
            continue
        yield line_nr, line

def skip_string(enumerate_lines):
    in_string = False
    in_comment = False
    for line_nr, line in enumerate_lines:
        # ignore comment markers inside string literals
        if not in_string:
            if "/-" in line:
                in_comment = True
            if "-/" in line:
                in_comment = False
        # ignore quotes inside comments
        if not in_comment:
            # crude heuristic: if the number of non-escaped quote signs is odd,
            # we're starting / ending a string literal
            if line.count("\"") - line.count("\\\"") % 2 == 1:
                in_string = not in_string
            # if there are quote signs in this line,
            # a string literal probably begins and / or ends here,
            # so we skip this line
            if line.count("\"") > 0:
                continue
            if in_string:
                continue
        yield line_nr, line

def small_alpha_vrachy_check(lines, path):
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if 'ᾰ' in line:
            errors += [(ERR_SAV, line_nr, path)]
    return errors

def reserved_notation_check(lines, path):
    if path.resolve() == RESERVED_NOTATION:
        return []
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if line.startswith('reserve') or line.startswith('precedence'):
            errors += [(ERR_RNT, line_nr, path)]
    return errors

def set_option_check(lines, path):
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if line.startswith('set_option'):
            next_two_chars = line.split(' ')[1][:2]
            # forbidden options: pp, profiler, trace
            if next_two_chars == 'pp' or next_two_chars == 'pr' or next_two_chars == 'tr':
                errors += [(ERR_OPT, line_nr, path)]
    return errors

def long_lines_check(lines, path):
    errors = []
    # TODO: some string literals (in e.g. tactic output messages) can be excepted from this rule
    for line_nr, line in enumerate(lines, 1):
        if "http" in line:
            continue
        if len(line) > 101:
            errors += [(ERR_LIN, line_nr, path)]
    return errors

def import_only_check(lines, path):
    import_only_file = True
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        imports = line.split()
        if imports[0] == "--":
            continue
        if imports[0] != "import":
            import_only_file = False
            break
        if len(imports) > 2:
            if imports[2] == "--":
                continue
            else:
                errors += [(ERR_IMP, line_nr, path)]
    return (import_only_file, errors)

def regular_check(lines, path):
    errors = []
    copy_started = False
    copy_done = False
    copy_start_line_nr = 0
    copy_lines = ""
    for line_nr, line in enumerate(lines, 1):
        if not copy_started and line == "\n":
            errors += [(ERR_COP, copy_start_line_nr, path)]
            continue
        if not copy_started and line == "/-\n":
            copy_started = True
            copy_start_line_nr = line_nr
            continue
        if not copy_started:
            errors += [(ERR_COP, line_nr, path)]
        if copy_started and not copy_done:
            copy_lines += line
            if line == "-/\n":
                if ((not "Copyright" in copy_lines) or
                    (not "Apache" in copy_lines) or
                    (not "Author" in copy_lines)):
                    errors += [(ERR_COP, copy_start_line_nr, path)]
                copy_done = True
            continue
        if copy_done and line == "\n":
            continue
        words = line.split()
        if words[0] != "import" and words[0] != "/-!":
            errors += [(ERR_MOD, line_nr, path)]
            break
        if words[0] == "/-!":
            break
        # final case: words[0] == "import"
        if len(words) > 2:
            if words[2] != "--":
                errors += [(ERR_IMP, line_nr, path)]
    return errors

def format_errors(errors):
    global new_exceptions
    for (errno, line_nr, path) in errors:
        if (errno, path.resolve()) in exceptions:
            continue
        new_exceptions = True
        # filename first, then line so that we can call "sort" on the output
        if errno == ERR_COP:
            print("{} : line {} : ERR_COP : Malformed or missing copyright header".format(path, line_nr))
        if errno == ERR_IMP:
            print("{} : line {} : ERR_IMP : More than one file imported per line".format(path, line_nr))
        if errno == ERR_MOD:
            print("{} : line {} : ERR_MOD : Module docstring missing, or too late".format(path, line_nr))
        if errno == ERR_LIN:
            print("{} : line {} : ERR_LIN : Line has more than 100 characters".format(path, line_nr))
        if errno == ERR_SAV:
            print("{} : line {} : ERR_SAV : File contains the character ᾰ".format(path, line_nr))
        if errno == ERR_RNT:
            print("{} : line {} : ERR_RNT : Reserved notation outside tactic.reserved_notation".format(path, line_nr))
        if errno == ERR_OPT:
            print("{} : line {} : ERR_OPT : Forbidden set_option command".format(path, line_nr))

def lint(path):
    with path.open() as f:
        lines = f.readlines()
        errs = long_lines_check(lines, path)
        format_errors(errs)
        (b, errs) = import_only_check(lines, path)
        if b:
            format_errors(errs)
            return
        errs = regular_check(lines, path)
        format_errors(errs)
        errs = small_alpha_vrachy_check(lines, path)
        format_errors(errs)
        errs = reserved_notation_check(lines, path)
        format_errors(errs)
        errs = set_option_check(lines, path)
        format_errors(errs)

for filename in sys.argv[1:]:
    lint(Path(filename))

# if "exceptions" is empty,
# we're trying to generate style-exceptions.txt,
# so new exceptions are expected
if new_exceptions and len(exceptions) > 0:
    exit(1)
