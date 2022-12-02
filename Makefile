.PHONY: prof

# generate Flamegraphs
prof:
	# build 
	stack build --profile
	# run & generate profile 
	stack exec --profile -- keelungc +RTS -p -poprofiling/exec
	# generate Flamegraph 
	cat profiling/exec.prof | ghc-prof-flamegraph > profiling/time.svg
	cat profiling/exec.prof | ghc-prof-flamegraph --alloc > profiling/space.svg

repl test: 
	stack repl keelung-compiler:test:keelung-test

# repl: 
# 	stack ghci keelung-compiler:exe:keelungc