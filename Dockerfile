FROM --platform=linux/amd64 haskell:9.2.5-slim as builder 
# for accessing private repositories
RUN  apt-get -yq update && \
     apt-get -yqq install ssh && \
     mkdir -p -m 0600 ~/.ssh && \
     ssh-keyscan github.com >> ~/.ssh/known_hosts
# copy the content of the repository to the container
COPY . . 
# grant access right to private repositories during the build process
RUN stack install
# multi-stage build
FROM --platform=linux/amd64 haskell:9.2.5-slim
# copy the built binary 
COPY --from=builder /root/.local/bin/keelungc /usr/local/bin/
ENTRYPOINT [ "keelungc" ]