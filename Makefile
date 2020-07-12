#### Edit these two for new files, not subsequent definitions
V_FILENAMES = Tactics.v Machine.v Json.v Opt.v ExampleParsers.v \
              Extract.v FusionExample.v
STATIC_ML_FILENAMES = runtime.ml
GEN_ML_FILENAMES    = p_json.ml example_parsers.ml \
	                    parse_3_2.ml parse_3_or_4.ml
BENCHMARKS = json sexp as ppm
####

V_FILES         = $(V_FILENAMES:%=theories/%)
STATIC_ML_FILES = $(STATIC_ML_FILENAMES:%=src/%)
GEN_ML_FILES    = $(GEN_ML_FILENAMES:%=src/%)
GEN_MLI_FILES   = $(GEN_ML_FILES:.ml=.mli)

ML_FILES = $(GEN_ML_FILES) $(STATIC_ML_FILES)
O_FILES  = $(ML_FILES:.ml=.o)

BINLOC = _build/default
BENCHLOC = src/benchmarks
BENCHMARK_TARGETS = $(BENCHMARKS:%=bench_%)
BENCHMARK_BUILD_NAMES = $(BENCHMARKS:%=src/benchmarks/bench_%.exe)

BENCH_QUOTA ?= 10

.PHONY: all extract clean

all: test

CoqMakefile: _CoqProject $(V_FILES)
	coq_makefile -f _CoqProject -o CoqMakefile

$(GEN_ML_FILES) : CoqMakefile
	$(MAKE) -f CoqMakefile

extract: CoqMakefile $(GEN_ML_FILES)

test: $(ML_FILES)
	cd src && dune runtest --profile release

$(BINLOC)/$(BENCHLOC)/bench_%.exe: $(BENCHLOC)/bench_%.ml $(ML_FILES) \
                                   $(BENCHLOC)/benchmarks.ml
	dune build $(BENCHLOC)/bench_$*.exe --profile release

bench_%: $(BINLOC)/$(BENCHLOC)/bench_%.exe
	ulimit -s unlimited; \
  ./$< -quota $(BENCH_QUOTA) -ci-absolute -clear-columns -all-values -ascii \
              +time alloc gc

benchmark: $(BENCHMARK_TARGETS)

prof_%: $(BINLOC)/$(BENCHLOC)/bench_%.exe
	ulimit -s unlimited; \
    perf record --call-graph=dwarf -- \
      $(BINLOC)/$(BENCHLOC)/bench_$*.exe -quota 1x
	perf report

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile
	rm -f $(GEN_ML_FILES) $(GEN_MLI_FILES)
