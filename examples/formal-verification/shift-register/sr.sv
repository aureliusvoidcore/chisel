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

