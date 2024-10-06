# Verification of Lookup Semantics for the Jolt zkVM





## Build Instructions

### Step 1: Install ACL2

1. Install Lisp:
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

### Step 2: Certify GL and FGL

1. Navigate to the ACL2 books directory:
   ```
   cd /path/to/acl2/books
   ```

2. Certify GL:
   ```
   cd /path/to/acl2/books/centaur/gl
   ../../build/cert.pl top.lisp
   ```


3. To certify FGL, we need to install an external SAT solver. The default choice is Glucose, which is included in this repository.

Simply run this Glucose installation script:
   ```
   ./install-glucose.sh
   ```

This script will compile Glucose, create a bash script to run it, and add it to your PATH.


4. Certify FGL:
   ```
   cd /path/to/acl2/books/centaur/fgl
   ../../build/cert.pl top.lisp
   ```


5. Add GL and FGL to your ACL2 initialization file:
   - Create or edit `~/.acl2rc`
   - Add the following lines:
     ```lisp
     (ld "/path/to/acl2/books/centaur/gl/gl-init.lisp")
     (ld "/path/to/acl2/books/centaur/fgl/fgl-init.lisp")
     ```
   Replace `/path/to/acl2` with the actual path to your ACL2 installation.


6. Verify installation:
   - Start ACL2: type `acl2` in your terminal
   - In the ACL2 prompt, try:
     ```lisp
     (gl::gl-satlink-config)
     (fgl::fgl-satlink-config)
     ```
   If these commands execute without errors, GL and FGL are properly installed.


### Step 3: Certify Subtables and Instructions

Check that our formalization is correct by certifying our `top` file:
```
/path/to/acl2/books/build/cert.pl top.lisp
```

### Step 4: Run Validation Script for Rust <> ACL2

Run the following script to validate the subtables. If this passes, then it means that the materialized subtables (for the size `2 ^ 16` as used in instruction lookups) are the same between Rust and ACL2.
```
./compare-subtables.sh
```

Run the following script to validate the instructions. This ensures that the expected instruction semantics are the same between Rust and ACL2, for certain specified inputs (see `print-instructions.lisp` for details).
```
./compare-instructions.sh
```