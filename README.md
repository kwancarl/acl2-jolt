# Verification of Lookup Semantics for the Jolt zkVM


## Project Structure

- `subtable` directory contains formalization of Lasso-style lookups, Jolt subtables, and multilinear extensions
- `instructions` directory contains formalization of Jolt instructions
- `jolt` directory contains a snapshot of the Jolt zkVM source code, with extra printing macros added in `jolt/jolt-core/src/jolt/subtable/print.rs` and `jolt/jolt-core/src/jolt/instruction/print.rs` for validation purposes


## Build Instructions

1. Follow the [official ACL2 instalation instructions](https://www.cs.utexas.edu/~moore/acl2/v8-5/HTML/installation/installation.html), which includes steps to:
   1. Install a Common Lisp implementation
   2. Install ACL2
   3. Certify some basic books 
2. Certify [GL](https://www.cs.utexas.edu/~moore/acl2/manuals/latest/?topic=ACL2____GL)

Note: MacOS laptops and Arm-based Apple silicon (e.g. M1) Macs are known to have issues with verifying Quicklisp books -- in both cases, the solution is to follow the [official ACL2 Quicklisp documentation](https://www.cs.utexas.edu/~moore/acl2/manuals/latest/?topic=ACL2____QUICKLISP):

1. Install OpenSSL via Homebrew
   ```
   brew install openssl
   ```
2. (If on Arm64 machine) Create symlinks to Homebrew’s OpenSSL library files in `/usr/local/lib`:
   ```
   ln -s /opt/homebrew/opt/openssl/lib/*.dylib /usr/local/lib
   ```

For convenience, we include the following instructions which worked for one author, but in case of any discrepancies between the official ACL2 instructions and the below, or in case of any installation issues, one should fall back to the official ACL2 instructions.

### Step 1: Install ACL2

1. Install Common Lisp:
   - For macOS (make sure Homebrew is installed): `brew install sbcl`
   - For Ubuntu: `sudo apt-get install sbcl`

2. Download ACL2:
   ```
   git clone https://github.com/acl2/acl2.git
   cd acl2
   ```

3. Build ACL2:
   ```
   make LISP=sbcl
   ```

4. Add ACL2 to your PATH:
   - For Bash: `echo 'export PATH=$PATH:/path/to/acl2/saved_acl2' >> ~/.bashrc`
   - For Zsh: `echo 'export PATH=$PATH:/path/to/acl2/saved_acl2' >> ~/.zshrc`
   Replace `/path/to/acl2` with the actual path where you cloned ACL2.

5. Reload your shell configuration:
   `source ~/.bashrc` or `source ~/.zshrc`

### Step 2: Certify GL

1. Navigate to the ACL2 books directory:
   ```
   cd /path/to/acl2/books
   ```

2. Certify GL:
   ```
   cd /path/to/acl2/books/centaur/gl
   ../../build/cert.pl top.lisp
   ```

5. Add GL to your ACL2 initialization file:
   - Create or edit `~/.acl2rc`
   - Add the following lines:
     ```lisp
     (ld "/path/to/acl2/books/centaur/gl/gl-init.lisp")
     ```
   Replace `/path/to/acl2` with the actual path to your ACL2 installation.


6. Verify installation:
   - Start ACL2: type `acl2` in your terminal
   - In the ACL2 prompt, try:
     ```lisp
     (gl::gl-satlink-config)
     ```
   If these commands execute without errors, GL and FGL are properly installed.


### Step 3: Certify Subtables and Instructions

Check that our formalization is correct by certifying our `top` file in the main directory:
```
/path/to/acl2/books/build/cert.pl top.lisp
```

### Step 4: Run Validation Script for Rust <> ACL2

Run the following script to validate the subtables. If this passes, then it means that the materialized subtables (for the size `2 ^ 16` as used in instruction lookups) are the same between Rust and ACL2.
```
./compare-subtables.sh
```

Run the following script to validate the instructions. This ensures that the instruction implementations in Rust and ACL2 produce the same results for a number of fuzzing inputs (see `print-instructions.lisp` for details).
```
./compare-instructions.sh
```
