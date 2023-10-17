# Automated building of a program out of source
#
# Just put the main program and libraries at the top here
# without extensions, and the makefile takes care of
# everything else:
SCM_PROGRAM = main
SCM_LIBS = libs/lib1 libs/lib2

# Don't edit below this line
#================================================================

.SECONDARY:

SRC_DIR = src/
BUILD_DIR = build/

SCM_LIBS_SRC = $(addprefix $(SRC_DIR), $(SCM_LIBS))
SCM_LIBS_OUT = $(addprefix $(BUILD_DIR), $(SCM_LIBS))
SCM_PROGRAM_SRC = $(addprefix $(SRC_DIR), $(SCM_PROGRAM))
SCM_PROGRAM_OUT = $(addprefix $(BUILD_DIR), $(SCM_PROGRAM))

SLD_FILES_SRC = $(addsuffix .sld, $(SCM_LIBS_SRC))
SLD_FILES_OUT = $(addsuffix .sld, $(SCM_LIBS_OUT))
SCM_FILE_SRC = $(addsuffix .scm, $(SCM_PROGRAM_SRC))
SCM_FILE_OUT = $(addsuffix .scm, $(SCM_PROGRAM_OUT))

META_FILES = $(addsuffix .meta, $(SCM_LIBS_OUT))
GENC_FILES = $(addsuffix .c, $(SCM_LIBS_OUT))
COBJECTS=$(SLD_FILES_OUT:.sld=.o)

all: $(SCM_PROGRAM_OUT)

run: $(SCM_PROGRAM_OUT)
	$<

$(BUILD_DIR)%.o: $(BUILD_DIR)%.sld
	cyclone -A $(BUILD_DIR) $<

$(BUILD_DIR)%.sld: $(SRC_DIR)%.sld
	mkdir -p $(@D)
	cp -f $< $@

$(BUILD_DIR)%.scm: $(SRC_DIR)%.scm
	mkdir -p $(@D)
	cp -f $< $@

$(SCM_PROGRAM_OUT): $(SCM_FILE_OUT) $(COBJECTS)
	cyclone -A $(BUILD_DIR) $<

#clean:
#	rm -ri $(BUILD_DIR)
