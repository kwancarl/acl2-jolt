#!/bin/sh

# Compile Glucose
cd ./glucose/simp
make

# Create bin directory if it doesn't exist
mkdir -p ./bin

# Create glucose script
echo '#!/bin/sh' > ./bin/glucose
echo '$(pwd)/glucose/simp/glucose -model "$@"' >> ./bin/glucose
chmod +x ./bin/glucose

# Determine the correct shell configuration file
if [ -n "$ZSH_VERSION" ]; then
    SHELL_CONFIG="$HOME/.zshrc"
elif [ -n "$BASH_VERSION" ]; then
    SHELL_CONFIG="$HOME/.bashrc"
else
    # Default to .profile if shell can't be determined
    SHELL_CONFIG="$HOME/.profile"
fi

# Add to PATH if not already present
if ! grep -q 'export PATH="$HOME/bin:$PATH"' "$SHELL_CONFIG"; then
    echo 'export PATH="$HOME/bin:$PATH"' >> "$SHELL_CONFIG"
fi

# Source the shell configuration file
source "$SHELL_CONFIG"

# Check if Glucose is installed correctly
if which glucose > /dev/null; then
    echo "Glucose installed successfully!"
    echo "Glucose location: $(which glucose)"
else
    echo "Error: Glucose installation failed. 'glucose' command not found in PATH."
    exit 1
fi