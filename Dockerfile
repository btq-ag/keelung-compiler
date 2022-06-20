FROM --platform=linux/amd64 haskell:8.10.7
# we expect the following directories to be available when building the image:
#   keelung/       - cloned from https://github.com/btq-ag/keelung
#   compiler/      - cloned from https://github.com/btq-ag/keelung-compiler  
COPY keelung keelung
COPY compiler compiler
# build the executable `keelungc` from compiler/
WORKDIR /compiler 
RUN stack install
ENTRYPOINT [ "keelungc" ]
