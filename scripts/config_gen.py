#!/usr/bin/env python3
import curses
import json
import os
import re
import glob
import sys
import argparse

CONFIG_FILE = "generation_config.json"
CMD_FILE = ".next_command"
SRC_DIR = "src/main/scala/examples"

def get_modules():
    modules = []
    # Match class definitions that extend BaseModule or Module
    pattern = re.compile(r"class\s+(\w+)(?:\[.*\])?\s*(?:\(.*\))?\s*extends\s+(\w+)")
    for filepath in glob.glob(os.path.join(SRC_DIR, "*.scala")):
        with open(filepath, 'r') as f:
            content = f.read()
            matches = pattern.findall(content)
            for class_name, parent_class in matches:
                if class_name == "BaseModule":
                    continue
                if parent_class not in ("BaseModule", "Module"):
                    continue
                modules.append(class_name)
    return sorted(list(set(modules)))

def default_config():
    return {
        "module": "PWMLEDAXI",
        "mode": "verification",
        "layers": "inline",
        "preserve_values": "named",
        "randomization": "disable",
        "run_formal": "no",
        "flow": "generate"
    }

def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r') as f:
                return json.load(f)
        except Exception:
            pass
    return default_config()

def save_config(config):
    with open(CONFIG_FILE, 'w') as f:
        json.dump(config, f, indent=2)

def draw_menu(stdscr, config, modules):
    curses.curs_set(0)
    curses.start_color()
    curses.init_pair(1, curses.COLOR_BLACK, curses.COLOR_CYAN)
    curses.init_pair(2, curses.COLOR_GREEN, curses.COLOR_BLACK)
    
    current_row = 0
    
    # Menu items structure
    # (Label, Key in config, Options list)
    menu_items = [
        ("Target Module", "module", modules),
        ("Flow", "flow", ["generate", "generate+formal"]),
        ("Generation Mode", "mode", ["verification", "synthesis"]),
        ("Layer Strategy", "layers", ["inline", "split"]),
        ("Preserve Values", "preserve_values", ["named", "all", "none"]),
        ("Randomization", "randomization", ["disable", "enable"]),
        ("Run Formal", "run_formal", ["no", "default", "k-induction", "ic3"])
    ]
    
    while True:
        stdscr.clear()
        h, w = stdscr.getmaxyx()
        
        # Title
        title = "Chisel Generation Configuration"
        stdscr.addstr(1, w//2 - len(title)//2, title, curses.A_BOLD | curses.color_pair(2))
        stdscr.addstr(2, w//2 - 15, "-"*30)

        # Draw Menu Items
        for idx, (label, key, options) in enumerate(menu_items):
            x = w//2 - 20
            y = 4 + idx * 2
            
            style = curses.A_NORMAL
            prefix = "   "
            if idx == current_row:
                style = curses.color_pair(1)
                prefix = "-> "
            
            current_val = config.get(key, options[0])
            display_str = f"{prefix}{label}: < {current_val} >"
            
            stdscr.addstr(y, x, display_str, style)

        # Instructions
        instr = "Use UP/DOWN to select, LEFT/RIGHT to change value. ENTER to Save & Exit. q to Quit."
        stdscr.addstr(h-2, w//2 - len(instr)//2, instr, curses.A_DIM)

        stdscr.refresh()
        
        key = stdscr.getch()
        
        if key == curses.KEY_UP:
            current_row = (current_row - 1) % len(menu_items)
        elif key == curses.KEY_DOWN:
            current_row = (current_row + 1) % len(menu_items)
        elif key == curses.KEY_LEFT:
            item = menu_items[current_row]
            key_name = item[1]
            options = item[2]
            curr_idx = options.index(config.get(key_name, options[0]))
            new_idx = (curr_idx - 1) % len(options)
            config[key_name] = options[new_idx]
        elif key == curses.KEY_RIGHT:
            item = menu_items[current_row]
            key_name = item[1]
            options = item[2]
            curr_idx = options.index(config.get(key_name, options[0]))
            new_idx = (curr_idx + 1) % len(options)
            config[key_name] = options[new_idx]
        elif key == ord('\n'): # Enter
            save_config(config)
            return True
        elif key == ord('q'):
            return False

def main(stdscr):
    config = load_config()
    modules = get_modules()
    if not modules:
        modules = ["PWMLEDAXI"] # Fallback
    
    return draw_menu(stdscr, config, modules)

def build_cmd(config):
    module = config.get("module", "PWMLEDAXI")
    flow = config.get("flow", "generate")
    run_formal = config.get("run_formal", "no")
    cmd = f"tools/sbt/bin/sbt \"runMain VerilogGenerator {module}\""
    if flow == "generate+formal" or run_formal != "no":
        cmd += f" && ./scripts/run_formal.sh {module} {run_formal}"
    return cmd


def run_non_interactive(args):
    config = load_config()
    # Override from CLI args if provided
    for key in ["module", "flow", "mode", "layers", "preserve_values", "randomization", "run_formal"]:
        val = getattr(args, key)
        if val:
            config[key] = val
    save_config(config)
    cmd = build_cmd(config)
    with open(CMD_FILE, "w") as f:
        f.write(cmd)
    if args.print_only:
        print(json.dumps(config, indent=2))
        print(f"Queued command: {cmd}")
    else:
        print(f"Configuration saved to {CONFIG_FILE}")
        print(f"Queued command in {CMD_FILE}: {cmd}")
    return 0


def parse_args():
    parser = argparse.ArgumentParser(description="Chisel menuconfig-like generator")
    parser.add_argument("--non-interactive", action="store_true", dest="non_interactive", help="Run without curses UI")
    parser.add_argument("--print", action="store_true", dest="print_only", help="Print config and command (non-interactive)")
    parser.add_argument("--module")
    parser.add_argument("--flow", choices=["generate", "generate+formal"])
    parser.add_argument("--mode", choices=["verification", "synthesis"])
    parser.add_argument("--layers", choices=["inline", "split"])
    parser.add_argument("--preserve_values", choices=["named", "all", "none"])
    parser.add_argument("--randomization", choices=["enable", "disable"])
    parser.add_argument("--run_formal", choices=["no", "default", "k-induction", "ic3"])
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    # Fallback to non-interactive if requested or no TTY available
    if args.non_interactive or not sys.stdin.isatty():
        sys.exit(run_non_interactive(args))

    try:
        if os.path.exists(CMD_FILE):
            os.remove(CMD_FILE)

        success = curses.wrapper(main)
        if success:
            print(f"Configuration saved to {CONFIG_FILE}")
            config = load_config()
            cmd = build_cmd(config)
            with open(CMD_FILE, "w") as f:
                f.write(cmd)
            print(f"Queued command in {CMD_FILE}: {cmd}")
        else:
            print("Configuration cancelled.")
            sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        print("Falling back to non-interactive mode with defaults.")
        sys.exit(run_non_interactive(args))
