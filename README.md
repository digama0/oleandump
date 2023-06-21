# `.olean` dump utility

This is based on https://github.com/gebner/oleanparser, but combines it with some typing information
scraped from lean itself so that we can determine what inductive constructors are being used.

Build it with `lake build`, use it like `lake exe oleandump FILE.olean MOD1 MOD2 ...`,
where `FILE.olean` is the file to dump and `MOD1 MOD2 ...` are modules that the dump tool itself
will load, which will help it resolve references inside the olean file.
