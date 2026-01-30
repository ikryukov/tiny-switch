"""Simple logging utility for tiny-switch tests."""

import os
from datetime import datetime

# Create logs directory if it doesn't exist
LOGS_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'logs')
os.makedirs(LOGS_DIR, exist_ok=True)


class Logger:
    """Simple file-based logger."""
    
    def __init__(self, name: str = "tswitch"):
        self.name = name
        self.test_name = None
        self.log_file = None
        self._file = None
        
    def configure(self, test_name: str):
        """Configure logger with test name. Creates a new log file if needed.
        
        Args:
            test_name: Name of the test (e.g., 'allreduce', 'multicast')
        """
        # If already configured with same test name, keep existing file
        if self.test_name == test_name and self._file is not None:
            return
            
        # Close existing file if open
        if self._file:
            self._file.close()
            self._file = None
            
        self.test_name = test_name
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_file = os.path.join(LOGS_DIR, f"log_{self.name}_{test_name}_{timestamp}.txt")
        
    def _ensure_file(self):
        if self._file is None:
            if self.log_file is None:
                # Fallback if configure() wasn't called - try to detect test name
                test_name = self._detect_test_name()
                self.test_name = test_name if test_name else None
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                if test_name:
                    self.log_file = os.path.join(LOGS_DIR, f"log_{self.name}_{test_name}_{timestamp}.txt")
                else:
                    self.log_file = os.path.join(LOGS_DIR, f"log_{self.name}_{timestamp}.txt")
            self._file = open(self.log_file, 'w')
    
    def _detect_test_name(self) -> str:
        """Try to detect test name from environment."""
        test_module = os.environ.get("COCOTB_TEST_MODULES", "")
        if test_module:
            name = test_module.split(".")[-1]
            if name.startswith("test_"):
                name = name[5:]
            return name
        return ""
            
    def info(self, message: str):
        """Log an info message."""
        self._ensure_file()
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        line = f"[{timestamp}] INFO: {message}"
        print(line)
        self._file.write(line + "\n")
        self._file.flush()
        
    def debug(self, message: str):
        """Log a debug message."""
        self._ensure_file()
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        line = f"[{timestamp}] DEBUG: {message}"
        self._file.write(line + "\n")
        self._file.flush()
        
    def warning(self, message: str):
        """Log a warning message."""
        self._ensure_file()
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        line = f"[{timestamp}] WARN: {message}"
        print(line)
        self._file.write(line + "\n")
        self._file.flush()
        
    def error(self, message: str):
        """Log an error message."""
        self._ensure_file()
        timestamp = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        line = f"[{timestamp}] ERROR: {message}"
        print(line)
        self._file.write(line + "\n")
        self._file.flush()
        
    def close(self):
        """Close the log file."""
        if self._file:
            self._file.close()
            self._file = None


# Global logger instance
logger = Logger()
