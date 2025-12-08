#include <ncurses.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>

#define ARRAY_SIZE(x) (int)(sizeof(x) / sizeof((x)[0]))
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

// Color pairs - Linux kernel style
#define COLOR_TITLE        1  // Blue background, white text
#define COLOR_MENU_NORMAL  2  // Normal menu items
#define COLOR_MENU_BOX     3  // Menu box border
#define COLOR_MENU_HL      4  // Highlighted menu item
#define COLOR_DIALOG_BOX   5  // Dialog box
#define COLOR_DIALOG_TEXT  6  // Dialog text
#define COLOR_BUTTON       7  // Button normal
#define COLOR_BUTTON_HL    8  // Button highlighted
#define COLOR_INPUTBOX     9  // Input box
#define COLOR_HELP        10  // Help text

struct option_entry {
    const char *name;
    const char *display_name;
    const char *desc;
    const char *help_text;
    const char **choices;
    int num_choices;
    int current;
};

static const char *modules[] = {
    "Adder", "Counter", "Mux2to1", "SimpleALU", "PWMLED", "PWMLEDAXI", "AbstractedPWMLEDAXI", "ShiftRegister"
};

static const char *modes[] = {"verification", "synthesis"};
static const char *layers[] = {"inline", "split"};
static const char *preserve_vals[] = {"named", "all", "none"};
static const char *rand_opts[] = {"disable", "enable"};
static const char *formal_opts[] = {"no", "default", "k-induction", "ic3"};

static void init_colors(void) {
    if (has_colors()) {
        start_color();
        
        // Linux kernel menuconfig "classic" theme
        init_pair(COLOR_TITLE, COLOR_YELLOW, COLOR_BLUE);         // Yellow on blue title
        init_pair(COLOR_MENU_NORMAL, COLOR_BLACK, COLOR_WHITE);   // Black on white/gray menu
        init_pair(COLOR_MENU_BOX, COLOR_BLUE, COLOR_CYAN);        // Blue box borders
        init_pair(COLOR_MENU_HL, COLOR_WHITE, COLOR_BLUE);        // White on blue highlight
        init_pair(COLOR_DIALOG_BOX, COLOR_BLACK, COLOR_WHITE);    // Dialog background
        init_pair(COLOR_DIALOG_TEXT, COLOR_BLACK, COLOR_WHITE);
        init_pair(COLOR_BUTTON, COLOR_BLACK, COLOR_WHITE);        // Black on white buttons
        init_pair(COLOR_BUTTON_HL, COLOR_WHITE, COLOR_BLUE);      // White on blue active
        init_pair(COLOR_INPUTBOX, COLOR_BLACK, COLOR_CYAN);
        init_pair(COLOR_HELP, COLOR_BLACK, COLOR_WHITE);
    }
    
    // Set background to cyan/blue
    bkgd(COLOR_PAIR(COLOR_MENU_BOX));
}

static void draw_box(int y, int x, int h, int w, int color_pair) {
    attron(COLOR_PAIR(color_pair));
    
    // Draw corners
    mvaddch(y, x, ACS_ULCORNER);
    mvaddch(y, x + w - 1, ACS_URCORNER);
    mvaddch(y + h - 1, x, ACS_LLCORNER);
    mvaddch(y + h - 1, x + w - 1, ACS_LRCORNER);
    
    // Draw horizontal lines
    mvhline(y, x + 1, ACS_HLINE, w - 2);
    mvhline(y + h - 1, x + 1, ACS_HLINE, w - 2);
    
    // Draw vertical lines
    mvvline(y + 1, x, ACS_VLINE, h - 2);
    mvvline(y + 1, x + w - 1, ACS_VLINE, h - 2);
    
    attroff(COLOR_PAIR(color_pair));
}

static void draw_shadow(int y, int x, int h, int w) {
    // Draw drop shadow for 3D effect
    attron(A_DIM);
    for (int i = 1; i < h; i++) {
        mvaddch(y + i, x + w, ' ');
        mvaddch(y + i, x + w + 1, ' ');
    }
    mvhline(y + h, x + 2, ' ', w);
    attroff(A_DIM);
}

static void draw_title_bar(void) {
    int width = COLS;
    attron(COLOR_PAIR(COLOR_TITLE) | A_BOLD);
    mvhline(0, 0, ' ', width);
    mvprintw(0, 2, " Chisel Project Configuration");
    mvprintw(0, width - 25, " <F1> for Help ");
    attroff(COLOR_PAIR(COLOR_TITLE) | A_BOLD);
}

static void draw_instruction_bar(void) {
    int y = LINES - 1;
    int width = COLS;
    
    attron(COLOR_PAIR(COLOR_TITLE));
    mvhline(y, 0, ' ', width);
    mvprintw(y, 2, "Arrows navigate | Enter selects | Tab=buttons | F5=Save | F6=Save&Exit | F9=Execute | F10=Exit");
    attroff(COLOR_PAIR(COLOR_TITLE));
}

static void show_help_dialog(struct option_entry *opt) {
    int dialog_w = MIN(COLS - 4, 76);
    int dialog_h = 18;
    int dialog_y = (LINES - dialog_h) / 2;
    int dialog_x = (COLS - dialog_w) / 2;
    
    // Draw shadow
    draw_shadow(dialog_y, dialog_x, dialog_h, dialog_w);
    
    // Fill dialog background
    attron(COLOR_PAIR(COLOR_DIALOG_BOX));
    for (int i = 0; i < dialog_h; i++) {
        mvhline(dialog_y + i, dialog_x, ' ', dialog_w);
    }
    attroff(COLOR_PAIR(COLOR_DIALOG_BOX));
    
    // Draw dialog box
    draw_box(dialog_y, dialog_x, dialog_h, dialog_w, COLOR_MENU_BOX);
    
    // Title
    attron(COLOR_PAIR(COLOR_TITLE) | A_BOLD);
    mvprintw(dialog_y, dialog_x + 2, " Help for '%s' ", opt->display_name);
    attroff(COLOR_PAIR(COLOR_TITLE) | A_BOLD);
    
    // Help text
    attron(COLOR_PAIR(COLOR_DIALOG_TEXT));
    int text_y = dialog_y + 2;
    int text_x = dialog_x + 2;
    int text_w = dialog_w - 4;
    
    // Word wrap the help text
    char *help = strdup(opt->help_text);
    char *line = help;
    char *next_line;
    int line_num = 0;
    
    while (line && line_num < dialog_h - 6) {
        next_line = strchr(line, '\n');
        if (next_line) {
            *next_line = '\0';
            next_line++;
        }
        
        // Word wrap if line is too long
        if ((int)strlen(line) > text_w) {
            int last_space = text_w - 1;
            while (last_space > 0 && line[last_space] != ' ') {
                last_space--;
            }
            if (last_space > 0) {
                char save = line[last_space];
                line[last_space] = '\0';
                mvprintw(text_y + line_num++, text_x, "%s", line);
                line[last_space] = save;
                line = line + last_space + 1;
                continue;
            }
        }
        
        mvprintw(text_y + line_num++, text_x, "%s", line);
        line = next_line;
    }
    
    free(help);
    
    // Available choices
    if (opt->num_choices > 1) {
        text_y = dialog_y + dialog_h - 5;
        attron(A_BOLD);
        mvprintw(text_y++, text_x, "Available options:");
        attroff(A_BOLD);
        for (int i = 0; i < opt->num_choices && text_y < dialog_y + dialog_h - 3; i++) {
            mvprintw(text_y++, text_x + 2, "%s %s",
                    i == opt->current ? "*" : " ", opt->choices[i]);
        }
    }
    attroff(COLOR_PAIR(COLOR_DIALOG_TEXT));
    
    // OK button
    int btn_y = dialog_y + dialog_h - 2;
    int btn_x = dialog_x + dialog_w / 2 - 5;
    attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    mvprintw(btn_y, btn_x, "< OK >");
    attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    
    refresh();
    
    // Wait for key press
    while (1) {
        int ch = getch();
        if (ch == '\n' || ch == ' ' || ch == 27) {
            break;
        }
    }
}

static void draw_menu(struct option_entry *opts, int nopts, int sel, int btn_sel) {
    int menu_h = nopts + 4;
    int menu_w = MIN(COLS - 6, 74);
    int menu_y = 2;
    int menu_x = (COLS - menu_w) / 2;
    
    erase();
    
    // Draw title bar
    draw_title_bar();
    
    // Draw main menu background (white/gray box with black text)
    attron(COLOR_PAIR(COLOR_MENU_NORMAL));
    for (int i = 0; i < menu_h; i++) {
        mvhline(menu_y + i, menu_x, ' ', menu_w);
    }
    attroff(COLOR_PAIR(COLOR_MENU_NORMAL));
    
    // Draw menu box border
    draw_box(menu_y, menu_x, menu_h, menu_w, COLOR_MENU_BOX);
    
    // Menu title
    attron(COLOR_PAIR(COLOR_TITLE) | A_BOLD);
    mvprintw(menu_y, menu_x + 2, " Configuration Options ");
    attroff(COLOR_PAIR(COLOR_TITLE) | A_BOLD);
    
    // Draw menu items
    for (int i = 0; i < nopts; i++) {
        int y = menu_y + i + 2;
        char line[128];
        
        // Format: "Display Name (value)"
        snprintf(line, sizeof(line), " %-28s (%s)", 
                 opts[i].display_name, 
                 opts[i].choices[opts[i].current]);
        
        if (i == sel) {
            attron(COLOR_PAIR(COLOR_MENU_HL) | A_BOLD);
            mvprintw(y, menu_x + 1, "%-*s", menu_w - 2, line);
            attroff(COLOR_PAIR(COLOR_MENU_HL) | A_BOLD);
        } else {
            attron(COLOR_PAIR(COLOR_MENU_NORMAL));
            mvprintw(y, menu_x + 1, "%s", line);
            attroff(COLOR_PAIR(COLOR_MENU_NORMAL));
        }
    }
    
    // Description panel at bottom
    int desc_y = menu_y + menu_h + 1;
    int desc_h = 6;
    int desc_w = menu_w;
    int desc_x = menu_x;
    
    // Draw description box
    attron(COLOR_PAIR(COLOR_MENU_NORMAL));
    for (int i = 0; i < desc_h; i++) {
        mvhline(desc_y + i, desc_x, ' ', desc_w);
    }
    attroff(COLOR_PAIR(COLOR_MENU_NORMAL));
    
    draw_box(desc_y, desc_x, desc_h, desc_w, COLOR_MENU_BOX);
    
    // Description title
    attron(COLOR_PAIR(COLOR_MENU_NORMAL) | A_BOLD);
    mvprintw(desc_y + 1, desc_x + 2, "%s", opts[sel].desc);
    attroff(COLOR_PAIR(COLOR_MENU_NORMAL) | A_BOLD);
    
    // Current value
    attron(COLOR_PAIR(COLOR_MENU_NORMAL));
    mvprintw(desc_y + 3, desc_x + 2, "Current: %s", opts[sel].choices[opts[sel].current]);
    attroff(COLOR_PAIR(COLOR_MENU_NORMAL));
    
    // Buttons at bottom
    int btn_y = desc_y + desc_h + 1;
    int btn_x = menu_x + 2;
    
    // Button 0: Select
    if (btn_sel == 0) {
        attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
        mvprintw(btn_y, btn_x, "<Select>");
        attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    } else {
        attron(COLOR_PAIR(COLOR_BUTTON));
        mvprintw(btn_y, btn_x, "<Select>");
        attroff(COLOR_PAIR(COLOR_BUTTON));
    }
    
    // Button 1: Help
    if (btn_sel == 1) {
        attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
        mvprintw(btn_y, btn_x + 12, "< Help >");
        attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    } else {
        attron(COLOR_PAIR(COLOR_BUTTON));
        mvprintw(btn_y, btn_x + 12, "< Help >");
        attroff(COLOR_PAIR(COLOR_BUTTON));
    }
    
    // Button 2: Save
    if (btn_sel == 2) {
        attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
        mvprintw(btn_y, btn_x + 24, "< Save >");
        attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    } else {
        attron(COLOR_PAIR(COLOR_BUTTON));
        mvprintw(btn_y, btn_x + 24, "< Save >");
        attroff(COLOR_PAIR(COLOR_BUTTON));
    }
    
    // Button 3: Execute
    if (btn_sel == 3) {
        attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
        mvprintw(btn_y, btn_x + 36, "< Execute >");
        attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    } else {
        attron(COLOR_PAIR(COLOR_BUTTON));
        mvprintw(btn_y, btn_x + 36, "< Execute >");
        attroff(COLOR_PAIR(COLOR_BUTTON));
    }
    
    // Button 4: Exit
    if (btn_sel == 4) {
        attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
        mvprintw(btn_y, btn_x + 51, "< Exit >");
        attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    } else {
        attron(COLOR_PAIR(COLOR_BUTTON));
        mvprintw(btn_y, btn_x + 51, "< Exit >");
        attroff(COLOR_PAIR(COLOR_BUTTON));
    }
    
    // Draw instruction bar
    draw_instruction_bar();
    
    refresh();
}

static void save_config(struct option_entry *opts) {
    const char *module = opts[0].choices[opts[0].current];
    const char *mode = opts[1].choices[opts[1].current];
    const char *layer = opts[2].choices[opts[2].current];
    const char *preserve = opts[3].choices[opts[3].current];
    const char *randopt = opts[4].choices[opts[4].current];
    const char *formal = opts[5].choices[opts[5].current];

    // Determine flow based on formal setting
    const char *flow = (strcmp(formal, "no") == 0) ? "generate" : "formal";

    FILE *f = fopen("generation_config.json", "w");
    if (!f) return;
    fprintf(f,
            "{\n"
            "  \"module\": \"%s\",\n"
            "  \"flow\": \"%s\",\n"
            "  \"mode\": \"%s\",\n"
            "  \"layers\": \"%s\",\n"
            "  \"preserve_values\": \"%s\",\n"
            "  \"randomization\": \"%s\",\n"
            "  \"run_formal\": \"%s\"\n"
            "}\n",
            module, flow, mode, layer, preserve, randopt, formal);
    fclose(f);

    f = fopen(".config.mk", "w");
    if (!f) return;
    fprintf(f, "MODULE=%s\nFLOW=%s\nMODE=%s\nLAYERS=%s\nPRESERVE=%s\nRANDOMIZATION=%s\nRUN_FORMAL=%s\n",
            module, flow, mode, layer, preserve, randopt, formal);
    fclose(f);
}

static void show_save_dialog(void) {
    int dialog_w = 50;
    int dialog_h = 7;
    int dialog_y = (LINES - dialog_h) / 2;
    int dialog_x = (COLS - dialog_w) / 2;
    
    draw_shadow(dialog_y, dialog_x, dialog_h, dialog_w);
    
    attron(COLOR_PAIR(COLOR_DIALOG_BOX));
    for (int i = 0; i < dialog_h; i++) {
        mvhline(dialog_y + i, dialog_x, ' ', dialog_w);
    }
    attroff(COLOR_PAIR(COLOR_DIALOG_BOX));
    
    draw_box(dialog_y, dialog_x, dialog_h, dialog_w, COLOR_MENU_BOX);
    
    attron(COLOR_PAIR(COLOR_DIALOG_TEXT) | A_BOLD);
    mvprintw(dialog_y + 2, dialog_x + 2, " Configuration saved successfully!");
    attroff(COLOR_PAIR(COLOR_DIALOG_TEXT) | A_BOLD);
    
    attron(COLOR_PAIR(COLOR_DIALOG_TEXT));
    mvprintw(dialog_y + 3, dialog_x + 2, " File: generation_config.json");
    attroff(COLOR_PAIR(COLOR_DIALOG_TEXT));
    
    attron(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    mvprintw(dialog_y + 5, dialog_x + dialog_w / 2 - 5, "< OK >");
    attroff(COLOR_PAIR(COLOR_BUTTON_HL) | A_BOLD);
    
    refresh();
    napms(1000);
}

static void run_flow(struct option_entry *opts) {
    const char *module = opts[0].choices[opts[0].current];
    const char *formal = opts[5].choices[opts[5].current];
    
    endwin();  // Exit ncurses before running commands
    
    printf("\n");
    printf("\033[1;36m========================================\033[0m\n");
    printf("\033[1;36m  Executing Configuration\033[0m\n");
    printf("\033[1;36m========================================\033[0m\n");
    printf("\033[1;33mModule:\033[0m %s\n", module);
    printf("\033[1;33mFormal:\033[0m %s\n", formal);
    printf("\033[1;36m========================================\033[0m\n\n");
    
    fflush(stdout);
    
    // Use apply-config target which reads .config.mk and executes the flow
    char cmd[512];
    snprintf(cmd, sizeof(cmd), "make apply-config");
    
    int ret = system(cmd);
    
    printf("\n");
    if (ret == 0) {
        printf("\033[1;32m========================================\033[0m\n");
        printf("\033[1;32m  Execution completed successfully!\033[0m\n");
        printf("\033[1;32m========================================\033[0m\n");
    } else {
        printf("\033[1;31m========================================\033[0m\n");
        printf("\033[1;31m  Execution failed with code %d\033[0m\n", ret);
        printf("\033[1;31m========================================\033[0m\n");
    }
    printf("\n");
    printf("Press Enter to continue...");
    getchar();
}

int main(void) {
    if (!isatty(0)) {
        fprintf(stderr, "menuconfig requires a TTY with ncurses.\n");
        return 1;
    }

    // Define menu options with detailed descriptions
    struct option_entry opts[] = {
        {
            "MODULE", 
            "Target Module",
            "Select the hardware module to generate",
            "Choose which Chisel module to compile into SystemVerilog.\n\n"
            "Available modules:\n"
            "- Adder: Simple 4-bit adder\n"
            "- Counter: 8-bit counter with enable\n"
            "- Mux2to1: Parameterized multiplexer\n"
            "- SimpleALU: Basic arithmetic/logic unit\n"
            "- PWMLED: PWM LED controller\n"
            "- PWMLEDAXI: PWM with AXI4-Lite interface\n"
            "- AbstractedPWMLEDAXI: Abstract AXI version\n"
            "- ShiftRegister: 4-stage shift register with LTL properties",
            modules, 
            ARRAY_SIZE(modules), 
            5
        },
        {
            "MODE", 
            "Generation Mode",
            "Verification or synthesis optimizations",
            "Select the optimization mode:\n\n"
            "- verification: Preserve signals and properties for formal\n"
            "  verification tools. Disables aggressive optimizations\n"
            "  that could remove assertions.\n\n"
            "- synthesis: Enable synthesis optimizations. May remove\n"
            "  debug signals and verification properties for better\n"
            "  area/timing. Use only for final implementation.",
            modes, 
            ARRAY_SIZE(modes), 
            0
        },
        {
            "LAYERS", 
            "Layer Mode",
            "Inline assertions or split with bind statements",
            "Control how verification properties are generated:\n\n"
            "- inline: Properties are emitted within ifdef guards in\n"
            "  the main module. Enabled/disabled with `define macros.\n"
            "  Best for single-file verification.\n\n"
            "- split: Properties in separate files with bind statements.\n"
            "  Better for modular verification and selective inclusion.\n"
            "  May require post-processing for some tools.",
            layers, 
            ARRAY_SIZE(layers), 
            0
        },
        {
            "PRESERVE", 
            "Preserve Values",
            "Signal name preservation level",
            "Control how signal names are preserved:\n\n"
            "- named: Preserve explicitly named signals (default).\n"
            "  Good balance of readability and optimization.\n\n"
            "- all: Preserve all intermediate signals and expressions.\n"
            "  Best for debugging but increases file size.\n\n"
            "- none: Minimal signal preservation. Aggressive optimization.\n"
            "  Smallest output but harder to debug.",
            preserve_vals, 
            ARRAY_SIZE(preserve_vals), 
            0
        },
        {
            "RANDOMIZATION", 
            "Randomization",
            "Initialize registers with random values",
            "Control register initialization:\n\n"
            "- disable: Initialize all registers to zero. Deterministic\n"
            "  behavior for formal verification and testing.\n\n"
            "- enable: Initialize with random values. Better for\n"
            "  simulation to catch initialization bugs. Not suitable\n"
            "  for formal verification.",
            rand_opts, 
            ARRAY_SIZE(rand_opts), 
            0
        },
        {
            "FORMAL_ENGINE", 
            "Formal Verification",
            "Formal verification algorithm selection",
            "Control formal verification execution and algorithm:\n\n"
            "- no: Generate SystemVerilog only. No formal verification.\n"
            "  Use this for initial generation or synthesis flow.\n\n"
            "- default: Generate + formal with bounded model checking.\n"
            "  Fast but only checks limited depth.\n\n"
            "- k-induction: Generate + formal using inductive proof.\n"
            "  Can prove properties for all time steps if inductive\n"
            "  invariant is found.\n\n"
            "- ic3: Generate + formal using IC3/PDR algorithm.\n"
            "  State-of-the-art method for proving properties.\n"
            "  Most powerful but may take longer.",
            formal_opts, 
            ARRAY_SIZE(formal_opts), 
            0
        }
    };
    
    int nopts = ARRAY_SIZE(opts);
    int sel = 0;
    int btn_sel = -1;  // -1 = menu mode, 0-4 = button mode

    if (initscr() == NULL) {
        fprintf(stderr, "Failed to init ncurses (check TERM).\n");
        return 1;
    }
    
    cbreak();
    noecho();
    keypad(stdscr, TRUE);
    curs_set(0);
    init_colors();

    draw_menu(opts, nopts, sel, btn_sel);

    int ch;
    int escape_count = 0;
    
    while (1) {
        ch = getch();
        
        if (ch == 27) {  // ESC
            escape_count++;
            if (escape_count >= 2) {
                break;
            }
            napms(200);  // Wait briefly for second ESC
            continue;
        } else {
            escape_count = 0;
        }
        
        switch (ch) {
            case KEY_UP:
            case 'k':
                if (btn_sel >= 0) {
                    // Exit button mode, go back to menu
                    btn_sel = -1;
                } else {
                    sel = (sel - 1 + nopts) % nopts;
                }
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case KEY_DOWN:
            case 'j':
                if (btn_sel >= 0) {
                    // Exit button mode, go back to menu
                    btn_sel = -1;
                } else {
                    sel = (sel + 1) % nopts;
                }
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case KEY_LEFT:
            case 'h':
                if (btn_sel >= 0) {
                    btn_sel = (btn_sel - 1 + 5) % 5;
                } else {
                    opts[sel].current = (opts[sel].current - 1 + opts[sel].num_choices) % opts[sel].num_choices;
                }
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case KEY_RIGHT:
            case 'l':
                if (btn_sel >= 0) {
                    btn_sel = (btn_sel + 1) % 5;
                } else {
                    opts[sel].current = (opts[sel].current + 1) % opts[sel].num_choices;
                }
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case ' ':
                if (btn_sel < 0) {
                    opts[sel].current = (opts[sel].current + 1) % opts[sel].num_choices;
                    draw_menu(opts, nopts, sel, btn_sel);
                }
                break;
                
            case '\t':
                // Tab enters button mode or cycles through buttons
                if (btn_sel < 0) {
                    btn_sel = 0;
                } else {
                    btn_sel = (btn_sel + 1) % 5;
                }
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case '\n':
                if (btn_sel == 0) {  // Select button
                    opts[sel].current = (opts[sel].current + 1) % opts[sel].num_choices;
                    draw_menu(opts, nopts, sel, btn_sel);
                } else if (btn_sel == 1) {  // Help button
                    show_help_dialog(&opts[sel]);
                    draw_menu(opts, nopts, sel, btn_sel);
                } else if (btn_sel == 2) {  // Save button
                    save_config(opts);
                    show_save_dialog();
                    draw_menu(opts, nopts, sel, btn_sel);
                } else if (btn_sel == 3) {  // Execute button
                    save_config(opts);
                    run_flow(opts);
                    // Reinitialize ncurses after execution
                    initscr();
                    cbreak();
                    noecho();
                    keypad(stdscr, TRUE);
                    curs_set(0);
                    init_colors();
                    draw_menu(opts, nopts, sel, btn_sel);
                } else if (btn_sel == 4) {  // Exit button
                    goto exit_loop;
                } else if (btn_sel < 0) {  // In menu, Enter cycles value
                    opts[sel].current = (opts[sel].current + 1) % opts[sel].num_choices;
                    draw_menu(opts, nopts, sel, btn_sel);
                }
                break;
                
            case '?':
            case KEY_F(1):
                show_help_dialog(&opts[sel]);
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case 's':
            case 'S':
            case KEY_F(5):  // F5 to save
                save_config(opts);
                show_save_dialog();
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case KEY_F(6):  // F6 to save and exit
                save_config(opts);
                goto exit_loop;
                
            case 'e':
            case 'E':
            case KEY_F(9):  // F9 to execute
                save_config(opts);
                run_flow(opts);
                // Reinitialize ncurses after execution
                initscr();
                cbreak();
                noecho();
                keypad(stdscr, TRUE);
                curs_set(0);
                init_colors();
                draw_menu(opts, nopts, sel, btn_sel);
                break;
                
            case 'q':
            case 'Q':
            case KEY_F(10):  // F10 to exit
                goto exit_loop;
                
            default:
                break;
        }
    }

exit_loop:
    endwin();
    
    save_config(opts);
    printf("\n");
    printf("\033[1;32m***\033[0m\n");
    printf("\033[1;32m***\033[0m Configuration written to \033[1mgeneration_config.json\033[0m\n");
    printf("\033[1;32m***\033[0m\n");
    printf("\n");
    
    return 0;
}
