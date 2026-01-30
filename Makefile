# tiny-switch Makefile
# Supports simulation with Icarus Verilog and linting with Verilator

.PHONY: all test compile lint format clean help

# ============== Configuration ==============
SIM ?= icarus
TOPLEVEL := tswitch
BUILD_DIR := build

# Source files
SRC_DIR := src
RTL_SOURCES := $(wildcard $(SRC_DIR)/*.sv)
RTL_CONVERTED := $(BUILD_DIR)/tswitch.v

# cocotb configuration
export LIBPYTHON_LOC := $(shell cocotb-config --libpython)
export PYGPI_PYTHON_BIN := $(shell cocotb-config --python-bin)

# ============== Main Targets ==============

all: test

# Create build directory
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Convert SystemVerilog to Verilog (sv2v)
$(RTL_CONVERTED): $(RTL_SOURCES) | $(BUILD_DIR)
	@echo "Converting SystemVerilog to Verilog..."
	sv2v -I $(SRC_DIR) $(RTL_SOURCES) -w $(BUILD_DIR)/tswitch_main.v
	@# Add timescale and combine
	echo '`timescale 1ns/1ns' > $@
	cat $(BUILD_DIR)/tswitch_main.v >> $@
	echo "" >> $@
	@rm -f $(BUILD_DIR)/tswitch_main.v

compile: $(RTL_CONVERTED)

# ============== Simulation ==============

# Build simulation executable
$(BUILD_DIR)/sim.vvp: $(RTL_CONVERTED)
	@echo "Compiling simulation..."
	iverilog -o $@ -s $(TOPLEVEL) -g2012 $<

# Run specific test
test_%: compile $(BUILD_DIR)/sim.vvp
	@echo "Running test: $*"
	COCOTB_TEST_MODULES=test.test_$* \
		vvp -M $$(cocotb-config --lib-dir) \
		-m libcocotbvpi_icarus \
		$(BUILD_DIR)/sim.vvp

# Run all tests (functional mode - fast)
test: test_allreduce test_multicast test_readwrite
	@echo "All tests completed!"

# Performance test targets (realistic latencies)
perf_%: compile $(BUILD_DIR)/sim.vvp
	@echo "Running performance test: $* (PerfLink latencies)"
	TEST_MODE=perflink COCOTB_TEST_MODULES=test.test_$* \
		vvp -M $$(cocotb-config --lib-dir) \
		-m libcocotbvpi_icarus \
		$(BUILD_DIR)/sim.vvp

# Run all tests with PerfLink latencies
perf: perf_allreduce perf_multicast perf_readwrite
	@echo "All performance tests completed!"

# ============== Linting ==============

# Lint flags: suppress sv2v conversion artifacts and intentional patterns
# - DECLFILENAME: sv2v outputs all modules to one file
# - ASCRANGE: sv2v generates ascending ranges for jump tables
# - WIDTHTRUNC/WIDTHEXPAND: sv2v converts '0 to 1'sb0
# - UNUSEDPARAM: sv2v extracts package constants as localparams
# - UNUSEDSIGNAL: sv2v uses 32-bit loop vars; some inputs reserved for future use
LINT_FLAGS := -Wall \
	--top-module $(TOPLEVEL) \
	-Wno-DECLFILENAME \
	-Wno-ASCRANGE \
	-Wno-WIDTHTRUNC \
	-Wno-WIDTHEXPAND \
	-Wno-UNUSEDPARAM \
	-Wno-UNUSEDSIGNAL

lint: $(RTL_CONVERTED)
	@echo "Running Verilator lint..."
	@verilator --lint-only $(LINT_FLAGS) $< 2>&1 && echo "Lint passed!" || true

lint-strict: $(RTL_CONVERTED)
	@echo "Running strict Verilator lint (all warnings)..."
	verilator --lint-only -Wall $< 2>&1 || true

lint-sv:
	@echo "Running Verilator lint on SystemVerilog..."
	verilator --lint-only -Wall -sv $(RTL_SOURCES) 2>&1 || true

# ============== Formatting ==============

# Format all SystemVerilog files in-place
format:
	@echo "Formatting SystemVerilog files..."
	@for f in $(RTL_SOURCES); do \
		verible-verilog-format --inplace $$f; \
	done
	@echo "Formatting complete!"

# Check formatting without modifying (for CI)
format-check:
	@echo "Checking SystemVerilog formatting..."
	@fail=0; for f in $(RTL_SOURCES); do \
		if ! verible-verilog-format --verify $$f >/dev/null 2>&1; then \
			echo "  $$f needs formatting"; \
			fail=1; \
		fi; \
	done; \
	if [ $$fail -eq 0 ]; then echo "Format check passed!"; else \
		echo "Format check failed. Run 'make format' to fix."; exit 1; \
	fi

# ============== Visualization ==============

# Generate schematic for a module
schematic_%: $(RTL_CONVERTED)
	@echo "Generating schematic for $*..."
	yosys -p "read_verilog $<; hierarchy -top $*; proc; opt; show -format svg -prefix $*_schematic" 2>/dev/null || \
	yosys -p "read_verilog $<; hierarchy -top $*; proc; opt; show -format dot -prefix $*_schematic"
	@[ -f $*_schematic.dot ] && dot -Tsvg $*_schematic.dot -o $*_schematic.svg && rm $*_schematic.dot || true
	@echo "Schematic saved to $*_schematic.svg"

# ============== Cleanup ==============

clean:
	rm -rf $(BUILD_DIR)
	rm -rf test/logs/log_*.txt
	rm -rf __pycache__ test/__pycache__ test/helpers/__pycache__
	rm -rf results.xml
	rm -rf *.svg *.dot

# ============== Help ==============

help:
	@echo "tiny-switch Build System"
	@echo ""
	@echo "Simulation:"
	@echo "  make compile         - Convert SV to Verilog"
	@echo "  make test_allreduce  - Run AllReduce test"
	@echo "  make test_multicast  - Run multicast test"
	@echo "  make test_readwrite  - Run read/write passthrough test"
	@echo "  make test            - Run all tests"
	@echo ""
	@echo "Linting & Formatting:"
	@echo "  make lint            - Lint converted Verilog with Verilator"
	@echo "  make lint-sv         - Lint SystemVerilog directly"
	@echo "  make format          - Format all SystemVerilog files"
	@echo "  make format-check    - Check formatting (CI-friendly)"
	@echo ""
	@echo "Visualization:"
	@echo "  make schematic_tswitch        - Generate top-level schematic"
	@echo "  make schematic_bf16_adder     - Generate BF16 adder schematic"
	@echo "  make schematic_reduction_engine - Generate reduction engine schematic"
	@echo ""
	@echo "Other:"
	@echo "  make clean           - Remove build artifacts"
	@echo "  make help            - Show this help"
