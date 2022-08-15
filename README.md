# The Keelung Compiler 

This repository contains proprietary stuff.
The compiler shall be distributed in the form of prebuilt binaries.

# Docker

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