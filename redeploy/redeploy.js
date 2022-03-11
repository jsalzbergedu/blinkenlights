#!/usr/bin/env node
let http = require('http')
const JSEncrypt = require('node-jsencrypt')
const {execSync} = require('child_process')

let pubkey = `
-----BEGIN PUBLIC KEY-----
MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQDApMe4Vza3UaxfURNQSDLFdzd8
L/ocnWc5Rz9/IIj2IahvHe7BDVvfRtyDhzWgTPDSg1SIX4tq4xiyzVrXosvhBwV8
JZsIBqFyoF8M201XFTlKPlcJzskzQcj3lR+U1n/rZ+7yhz58FHo9RdxVsvSqUiE6
XZV9QmJdFn3f0bsVkQIDAQAB
-----END PUBLIC KEY-----
`

http.createServer(
    async function(req, res) {
        const buffers = [];
        for await (const chunk of req) {
            buffers.push(chunk);
        }
        const body = Buffer.concat(buffers).toString();
        let encrypt = new JSEncrypt();
        encrypt.setPublicKey(pubkey)
        const randomString = Math.random().toString().substr(2, 8)
        let encrypted = encrypt.encrypt(randomString);
        let decrypt = new JSEncrypt();
        decrypt.setPrivateKey(body);
        if (decrypt.decrypt(encrypted) == randomString) {
            console.log("successful decryption")
            execSync('bash redeploy/redeploy.sh')
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({
                data: 'successful redeploy'
            }));
        } else {
            console.log("unsuccessful decryption")
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({
                data: 'unsuccessful decryption'
            }));
        }
    }
).listen(8080)


