FROM --platform=linux/amd64 haskell:8.10.7
COPY keelung keelung
COPY compiler compiler
WORKDIR /compiler 
RUN stack install
ENTRYPOINT [ "keelungc" ]
