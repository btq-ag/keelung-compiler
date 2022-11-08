# The Keelung Compiler 

This repository contains proprietary stuff.
The compiler shall be distributed in the form of prebuilt binaries.

# How to dockerize `keelungc`

To dockerize the executable `keelungc`, run the following command in the root of the repository:

```bash 
DOCKER_BUILDKIT=1  docker build --ssh default -t keelung -f Dockerfile .
```

(add `--platform linux/amd64` if you are using architectures like arm64)

The built image is currently available on the Docker Hub as [banacorn/keelung](https://hub.docker.com/repository/docker/banacorn/keelung).

To execute the image, run:

```
docker run banacorn/keelung
```

(add `--platform linux/amd64` if you are using architectures like arm64)

# How to profile the compiler and generate flamegraphs

1. Install [ghc-prof-flamegraph](https://hackage.haskell.org/package/ghc-prof-flamegraph) on your machine: 

```bash
stack install ghc-prof-flamegraph
```

2. Prepare an executable like `profile` in `profiling/Main.hs` with the program you want to profile.
3. Build and install the executable with profiling enabled:

```bash
stack install keelung-compiler:exe:profile --profile
``` 

4. Generate a profiling report:

```bash
stack exec --profile -- profile +RTS -p
```

5. Generate a flamegraph:

```bash
ghc-prof-flamegraph profile.prof
``` 