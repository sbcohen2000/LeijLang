SRC_DIR  = src
OUT_DIR  = build
BIN_DIR  = bin
RUN_DIR  = runtime
TEST_DIR = tests

MLTON_OPTS = -default-ann 'allowExtendedTextConsts true'

SOURCES = $(wildcard $(SRC_DIR)/*)

$(BIN_DIR)/lc: $(SOURCES) | build bin
	cp $(SOURCES) build
	cd $(OUT_DIR); mlton $(MLTON_OPTS) lc.mlb
	rm $(patsubst $(SRC_DIR)/%, $(OUT_DIR)/%, $(SOURCES))
	cp $(OUT_DIR)/lc $(BIN_DIR)

$(OUT_DIR):
	mkdir -p $@

$(BIN_DIR):
	mkdir -p $@

check: $(BIN_DIR)/lc
	ruby check.rb $(TEST_DIR)

clean:
	rm -rf $(OUT_DIR) $(BIN_DIR)

.PHONY: clean check
