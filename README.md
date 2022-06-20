# The Keelung Compiler 

This repository contains proprietary stuff.
The compiler shall be distributed in the form of prebuilt binaries.

# Docker

To dockerize the executable `keelungc`, please clone the following repositories:

* `keelung/`: cloned from https://github.com/btq-ag/keelung
* `compiler/`: cloned from https://github.com/btq-ag/keelung-compiler  

And place them side by side like this:

```
.
├── keelung/
└── compiler/
```

Run the following command from the parent directory of the cloned repositories:

```
docker build -t keelung -f compiler/Dockerfile .
```

(add `--platform linux/amd64` if you are using architectures like arm64)

The built image is currently available on the Docker Hub as [banacorn/keelung](https://hub.docker.com/repository/docker/banacorn/keelung).

To execute the image, run:

```
docker run banacorn/keelung
```

(add `--platform linux/amd64` if you are using architectures like arm64)