# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import os

dream_dir = os.path.dirname(__file__)

PROLOG = {
    "predicates": os.path.join(dream_dir, "prolog/predicates.pl"),
    "rules": os.path.join(dream_dir, "prolog/rules.pl"),
    "builtin_rules": os.path.join(dream_dir, "prolog/builtin_rules.pl"),
    "queries": os.path.join(dream_dir, "prolog/queries"),
    "named_constants_rules": os.path.join(dream_dir, "prolog/named_constants_rules.pl"),
}

IMPORTS = os.path.join(dream_dir, "prolog/imports.json")
