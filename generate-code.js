#!/usr/bin/env node

const { generate } = require("astring");
const { createInterface } = require("readline");

const read = () => new Promise((resolve) => {
    process.stdin.setEncoding("utf-8");

    const reader = createInterface({ input: process.stdin });

    let content = "";
    let first = true;

    reader.on("line", (line) => {
        content += first ? line : `\n${line}`;
        first = false;
    });

    reader.on("close", () => {
        resolve(content);
    });
});

(async () => {
    const content = await read();
    const ast = JSON.parse(content);
    console.log(generate(ast).trimEnd());
})();
