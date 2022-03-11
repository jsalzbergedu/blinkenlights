#!/bin/bash
echo "attempting redeployment"
OLD_COMMIT="$(git rev-parse HEAD)"
git pull
NEW_COMMIT="$(git rev-parse HEAD)"
cd ./server
if [ "$OLD_COMMIT" != "$NEW_COMMIT" ]
then
    echo "attempting redeployment"
    cargo build --release
    kill $(pidof "blinkenlights-server")
    cargo run --release
fi
