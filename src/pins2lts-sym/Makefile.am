HRE_LIB = ../hre/libhre.la
SYM_CPP_FLAGS = $(AM_CPPFLAGS) $(PROFILER_CPPFLAGS)
SYM_LD_FLAGS = $(AM_LDFLAGS) $(PROFILER_LDFLAGS)
PINS_LIBS  =
PINS_LIBS += ../lts-io/liblts-io.la
PINS_LIBS += ../hre-io/libhre-io.la
PINS_LIBS += $(HRE_LIB)
PINS_LIBS += ../pins-lib/libpins.la
PINS_LIBS += ../ltsmin-lib/libltsmin.la
PINS_LIBS += ../util-lib/libutil.la
PINS_LIBS += ../dm/libdm.la
PINS_LIBS += ../spg-lib/libspg.la

VSET_LIBS = ../vset-lib/libvset.la

bin_PROGRAMS = etf2lts-sym pins2lts-sym

if HAVE_LIBSTEP_INFO
bin_PROGRAMS += lpo2lts-sym
endif

if HAVE_LIBMCRL2
bin_PROGRAMS += lps2lts-sym
endif

if HAVE_SCOOP
bin_PROGRAMS += mapa2lts-sym
endif

if HAVE_LIBPBES
bin_PROGRAMS += pbes2lts-sym
endif

if HAVE_DVE
bin_PROGRAMS += dve2lts-sym
endif

if HAVE_SPINS
bin_PROGRAMS += prom2lts-sym
endif

if HAVE_SYLVAN
SYM_CPP_FLAGS += $(SYLVAN_CPPFLAGS)
endif

# etf2lts-sym
etf2lts_sym_SOURCES   = pins2lts-sym.c
etf2lts_sym_SOURCES  += ../pins-lib/etf-pins.c ../pins-lib/etf-pins.h
etf2lts_sym_LDADD     = $(PINS_LIBS) $(VSET_LIBS)
etf2lts_sym_CPPFLAGS  = -DETF $(SYM_CPP_FLAGS)
etf2lts_sym_LDFLAGS   = $(SYM_LDFLAGS)
nodist_EXTRA_etf2lts_sym_SOURCES = automake-force-linker.cxx # req. by vset

# pins2lts-sym
pins2lts_sym_SOURCES   = pins2lts-sym.c
pins2lts_sym_SOURCES  += ../pins-lib/dlopen-pins.c ../pins-lib/dlopen-pins.h
pins2lts_sym_LDADD     = $(PINS_LIBS) $(VSET_LIBS)
pins2lts_sym_CPPFLAGS  = -DPINS_DLL $(SYM_CPP_FLAGS)
if !BUILD_OS_IS_DARWIN
pins2lts_sym_LDFLAGS   = -Wl,-E $(SYM_LD_FLAGS)
endif
nodist_EXTRA_pins2lts_sym_SOURCES = automake-force-linker.cxx # req. by vset

# lpo2lts-sym
lpo2lts_sym_SOURCES   = pins2lts-sym.c
lpo2lts_sym_LDADD     = $(PINS_LIBS)
lpo2lts_sym_LDADD    += ../pins-lib/libmcrl-pins.la
lpo2lts_sym_LDADD    += $(VSET_LIBS) $(MCRL_LIBS)
lpo2lts_sym_CPPFLAGS  = -DMCRL $(MCRL_CPPFLAGS) $(SYM_CPP_FLAGS)
lpo2lts_sym_LDFLAGS   = $(MCRL_LDFLAGS) $(SYM_LD_FLAGS)
nodist_EXTRA_lpo2lts_sym_SOURCES = automake-force-linker.cxx # req. by mcrl

# lps2lts-sym
lps2lts_sym_SOURCES   = pins2lts-sym.c
lps2lts_sym_LDADD     = $(PINS_LIBS)
lps2lts_sym_LDADD    += ../pins-lib/libmcrl2-pins.la
lps2lts_sym_LDADD    += $(VSET_LIBS) $(MCRL2_LIBS)
lps2lts_sym_CPPFLAGS  = -DMCRL2 $(SYM_CPP_FLAGS)
lps2lts_sym_LDFLAGS   = $(MCRL2_LDFLAGS) $(SYM_LD_FLAGS)
nodist_EXTRA_lps2lts_sym_SOURCES = automake-force-linker.cxx # req. by mcrl2

# mapa2lts-sym
mapa2lts_sym_SOURCES   = pins2lts-sym.c
mapa2lts_sym_LDADD     = ../pins-lib/libmapa-pins.la
mapa2lts_sym_LDADD    += $(PINS_LIBS) $(VSET_LIBS) -lscoop
mapa2lts_sym_LDFLAGS   = -Wl,-rpath,$(DESTDIR)$(pkglibdir) $(SCOOP_LDFLAGS) -L${top_builddir}/scoop/src $(SYM_LD_FLAGS) -Wl,-lscoop
mapa2lts_sym_CPPFLAGS  = -DMAPA $(SYM_CPP_FLAGS)
nodist_EXTRA_mapa2lts_sym_SOURCES = automake-force-linker.cxx # req. by vset

# pbes2lts-sym
pbes2lts_sym_SOURCES   = pins2lts-sym.c
pbes2lts_sym_LDADD     = $(PINS_LIBS)
pbes2lts_sym_LDADD    += $(VSET_LIBS) ../pins-lib/libpbes-pins.la
pbes2lts_sym_CPPFLAGS  = -DLTSMIN_PBES $(SYM_CPP_FLAGS)
pbes2lts_sym_LDFLAGS   = $(MCRL2_LDFLAGS) $(SYM_LD_FLAGS)
nodist_EXTRA_pbes2lts_sym_SOURCES = automake-force-linker.cxx # req. by pbes

# dve2lts-sym
dve2lts_sym_SOURCES   = pins2lts-sym.c
dve2lts_sym_SOURCES  += ../pins-lib/dve-pins.c ../pins-lib/dve-pins.h
dve2lts_sym_LDADD     = $(PINS_LIBS)
dve2lts_sym_LDADD    += $(VSET_LIBS) $(DVE_LIBS)
dve2lts_sym_CPPFLAGS  = -DDIVINE $(DIVINE_CPPFLAGS) $(SYM_CPP_FLAGS)
dve2lts_sym_LDFLAGS   = $(DIVINE_LDFLAGS) $(SYM_LD_FLAGS)
nodist_EXTRA_dve2lts_sym_SOURCES = automake-force-linker.cxx # req. by vset

# prom2lts-sym
prom2lts_sym_SOURCES  = pins2lts-sym.c
prom2lts_sym_SOURCES += ../pins-lib/prom-pins.c ../pins-lib/prom-pins.h
prom2lts_sym_LDADD    = $(PINS_LIBS)
prom2lts_sym_LDADD   += $(VSET_LIBS) $(SPINS_LIBS)
prom2lts_sym_CPPFLAGS = -DSPINS $(SPINS_CPPFLAGS) $(SYM_CPP_FLAGS)
prom2lts_sym_LDFLAGS  = $(SPINS_LDFLAGS) $(SYM_LD_FLAGS)
nodist_EXTRA_prom2lts_sym_SOURCES = automake-force-linker.cxx # req. by vset
