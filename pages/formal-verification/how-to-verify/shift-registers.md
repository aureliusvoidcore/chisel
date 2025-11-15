---
layout: default
title: Shift registers/pipelines
permalink: /pages/formal-verification/how-to-verify/shift-registers
---

# Shift registers/pipelines

## sr.sv


```systemverilog
module shift_reg #(
    parameter int unsigned WIDTH = 1024
) (
    input wire clk,
    input wire rstn,
    input wire en,
    input wire din,
    output logic dout
);

    logic [WIDTH-1:0] sr;
    logic after_reset;

    always @(posedge clk) begin
        if (!rstn) begin
            sr <= '0;
            after_reset <= 1'b1;
        end else begin
            after_reset <= 1'b0;
            if (en) begin
                sr <= {din, sr[WIDTH-1:1]};
            end
        end
    end

    assign dout = sr[0];

   main: assert property
   ( @(posedge clk) disable iff (!rstn || after_reset)
     ((sr === $past(sr)) || ($past(en) === 1'b1))
     &&
     ((sr === {$past(din), $past(sr[WIDTH-1:1])}) || ($past(en) === 1'b0)) );
endmodule // shift_reg
```

<!-- Interactive EBMC runner: minimal controls -->
<div class="panel" style="margin: 1rem 0; padding: 0.75rem; border: 1px solid var(--accent1, #0ff); border-radius: 6px;">
    <div style="display: flex; gap: 0.5rem; align-items: center; flex-wrap: wrap; margin-bottom: 0.5rem;">
        <label for="sr-extra-args" style="font-weight: 600;">Extra args:</label>
        <input id="sr-extra-args" type="text" placeholder="e.g. --k-induction --unwind 10" style="flex: 1 1 320px; min-width: 240px; padding: 0.4rem 0.6rem; background: rgba(255,255,255,0.03); color: inherit; border: 1px solid rgba(255,255,255,0.2); border-radius: 4px;" />
        <button id="sr-run" class="button" type="button">Run EBMC</button>
        <button id="sr-clear" class="button button-secondary" type="button">Clear</button>
    </div>
    <div style="font-family: var(--mono, 'Share Tech Mono', monospace); font-size: 0.95rem; line-height: 1.4;">
        <div style="opacity: 0.8; margin-bottom: 0.25rem;">Command: <code>ebmc --systemverilog design.v --reset "~rstn"</code> <span style="opacity:0.7">+ extra args</span></div>
        <pre id="sr-output" style="margin: 0; max-height: 360px; overflow: auto; padding: 0.75rem; background: rgba(0,0,0,0.55); border: 1px solid rgba(255,255,255,0.12); border-radius: 4px;"></pre>
    </div>
</div>

<script src="{{ site.baseurl }}/hwcbmc_build/hwcbmc.js?v=20251115a"></script>
<script src="{{ site.baseurl }}/hwcbmc_build/hwcbmc-wrapper.js?v=20251115a"></script>
<script>window.__siteBaseUrl='{{ site.baseurl }}';</script>
<script src="{{ site.baseurl }}/assets/js/hwcbmc-mini.js?v=20251115a"></script>
