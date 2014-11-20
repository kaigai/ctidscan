# contrib/ctidscan/Makefile

MODULES = ctidscan

EXTENSION = ctidscan

REGRESS = ctidscan

PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
