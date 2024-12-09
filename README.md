# Dependencies

GNU Make

Compatible with Coq 8.18-8.19

# Build Command

```sh
git submodule update --init

# apply patch if compilation failed
cd <subdir>
git apply ../xx-<subdir>.patch
cd ..

make world
make
```
