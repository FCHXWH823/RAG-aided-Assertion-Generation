//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Module - PNSeqGen
//Pseudo-random pattern generator

module PNSeqGen(
  input        clk,
  input        rst_n,
  output [1:0] rand_n
  );

reg s1, s2, s3;
wire s0;

assign s0 = s1 ^ s3;

always @ (posedge clk or negedge rst_n) begin
  if(!rst_n) begin
   s1 <= 1;
   s2 <= 0;
   s3 <= 0;
  end else begin   
   s1 <= s0;
   s2 <= s1;
   s3 <= s2;
  end
end

assign rand_n = {s3,s2};

endmodule
//Lab 4 - Formal Property Verification
//
//
//Module - arbiter
//4-way arbiter with multiple arbitration schemes

module arbiter(
  clk,
  rst_n,
  req,
  arb_type,
  gnt
  );

// Input and Output ports
input        clk;
input        rst_n;
input  [3:0] req;
input  [2:0] arb_type;

output [3:0] gnt;

// Internal variables
wire [3:0] req;

reg  [3:0] r_gnt_p0; // P0 priority scheme output
reg  [3:0] r_gnt_p1; // P1 priority scheme output
reg  [3:0] r_gnt_p2; // P2 priority scheme output
reg  [3:0] r_gnt_p3; // P3 priority scheme output
reg  [3:0] r_gnt_rr; // Prr: Round robin arbitration scheme output
reg  [3:0] r_gnt_px; // Prand: Random arbitration scheme output
reg  [3:0] r_gnt;

wire [1:0] rand_n;
wire [1:0] r_gnt_rr_encoded;

assign gnt   = r_gnt;

// P0 Fixed Priority req[0]
always @(*) begin
  if(req[0])
    r_gnt_p0 = 4'b0001;
  else if(req[1])
    r_gnt_p0 = 4'b0010;
  else if(req[2])
    r_gnt_p0 = 4'b0100;
  else if(req[3])
    r_gnt_p0 = 4'b1000; // Saqib changed this from r_gnt_p0 = 4'b0000;
  else
    r_gnt_p0 = 4'b0000;
end

// P1 Fixed Priority req[1]
always @(*) begin
  if(req[1])
    r_gnt_p1 = 4'b0010;
  else if(req[0])
    r_gnt_p1 = 4'b0001;
  else if(req[2])
    r_gnt_p1 = 4'b0100;
  else if(req[3])
    r_gnt_p1 = 4'b1000;
  else
    r_gnt_p1 = 4'b0000;
end

// P2 Fixed Priority req[2]
always @(*) begin
  if(req[2])
    r_gnt_p2 = 4'b0100;
  else if(req[0])
    r_gnt_p2 = 4'b0001;
  else if(req[1])
    r_gnt_p2 = 4'b0010;
  else if(req[3])
    r_gnt_p2 = 4'b1000;
  else
    r_gnt_p2 = 4'b0000;
end

// P3 Fixed Priority req[3]
always @(*) begin
  if(req[3])
    r_gnt_p3 = 4'b1000;
  else if(req[0])
    r_gnt_p3 = 4'b0001;
  else if(req[1])
    r_gnt_p3 = 4'b0010;
  else if(req[2])
    r_gnt_p3 = 4'b0100;
  else
    r_gnt_p3 = 4'b0000;
end

// Prr: Round robin arbiter
always @ (*) begin
  r_gnt_rr[0] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & req[0]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & req[0]) |
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[3] & ~req[2] & req[0]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & ~req[2] & ~req[1] & req[0]) ;

  r_gnt_rr[1] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[0] & req[1]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & ~req[0] & req[1]) |
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[3] & ~req[2] & ~req[0] & req[1]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & req[1]) ;
  
  r_gnt_rr[2] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[0] & ~req[1] & req[2]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & ~req[0] & ~req[1] & req[2]) |  // Saqib changed req[1] to ~req[1]
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & req[2]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[1] & req[2]) ;
 
  r_gnt_rr[3] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[0] & ~req[1] & ~req[2] & req[3]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & req[3]) |
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[2] & req[3]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[1] & ~req[2] & req[3]) ;
end

// encode the 4b r_gnt_rrs to 2b
assign r_gnt_rr_encoded = {r_gnt[3] | r_gnt[2], r_gnt[3] | r_gnt[1]};

// Prand: Random arbitration
PNSeqGen u_PNSeqGen ( .clk(clk), .rst_n(rst_n), .rand_n(rand_n) );

always @(*) begin
  case(rand_n)

  2'b00: begin
    if(req[0])
      r_gnt_px = 4'b0001;
    else if(req[1])
      r_gnt_px = 4'b0010;
    else if(req[2])
      r_gnt_px = 4'b0100;
    else if(req[3])
      r_gnt_px = 4'b1000;
    else
      r_gnt_px = 4'b0000;
  end
  
  2'b01: begin
    if(req[1])
      r_gnt_px = 4'b0010;  // Saqib change 4'b0001 to 4'b0010
    else if(req[0])
      r_gnt_px = 4'b0001;  // Saqib change 4'b0010 to 4'b0001
    else if(req[2])
      r_gnt_px = 4'b0100;
    else if(req[3])
      r_gnt_px = 4'b1000;
    else
      r_gnt_px = 4'b0000;
  end

  2'b10: begin
    if(req[2])
      r_gnt_px = 4'b0100;
    else if(req[0])
      r_gnt_px = 4'b0001;
    else if(req[1])
      r_gnt_px = 4'b0010;
    else if(req[3])
      r_gnt_px = 4'b1000;
    else
      r_gnt_px = 4'b0000;
  end

  2'b11: begin
    if(req[3])
      r_gnt_px = 4'b1000;
    else if(req[0])
      r_gnt_px = 4'b0001;
    else if(req[1])
      r_gnt_px = 4'b0010;
    else if(req[2])
      r_gnt_px = 4'b0100;
    else
      r_gnt_px = 4'b0000;
  end

  endcase
end

// Priority selection
always @(posedge clk or negedge rst_n)
begin
  if(!rst_n)
    r_gnt <= 4'b0000;
  else
    case(arb_type)
      4'b0000: r_gnt <= r_gnt_p0;
      4'b0001: r_gnt <= r_gnt_p1;
      4'b0010: r_gnt <= r_gnt_p2;
      4'b0011: r_gnt <= r_gnt_p3;
      4'b0100: r_gnt <= r_gnt_rr;
      4'b0101: r_gnt <= r_gnt_px;
      default: r_gnt <= 4'b0000;
    endcase
end


assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd0)) |-> $past(req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd0)) |-> $past(req[1] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd0)) |-> $past(req[2] & ~req[1] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd0)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd1)) |-> $past(req[0] & ~req[1]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd1)) |-> $past(req[1]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd1)) |-> $past(req[2] & ~req[1] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd1)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd2)) |-> $past(req[0] & ~req[2]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd2)) |-> $past(req[1] & ~req[2] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd2)) |-> $past(req[2]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd2)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd3)) |-> $past(req[0] & ~req[3]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd3)) |-> $past(req[1] & ~req[3] & ~req[0]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd3)) |-> $past(req[2] & ~req[3] & ~req[0] & ~req[1]));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd3)) |-> $past(req[3]));

assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] ##1 (arb_type == 3'b000)) |-> req[0][*1]));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] && $past(arb_type == 3'd0)) |-> $past(req[0])) iff ((gnt[0] ##1 (arb_type == 3'b000)) |-> req[0][*1]));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] && (arb_type == 3'b000)) |-> (req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] && $past(arb_type == 3'd0)) |-> $past(req[1] & ~req[0])) iff ((gnt[1] && (arb_type == 3'b000)) |-> (req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] == 1) && (arb_type == 3'b000) |->          (req[2] |->1) && !req[0] && !req[1]));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] && $past(arb_type == 3'd0)) |-> $past(req[2] & ~req[1] & ~req[0])) iff ((gnt[2] == 1) && (arb_type == 3'b000) |->          (req[2] |->1) && !req[0] && !req[1]));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[3] && arb_type == 3'b000) |-> (req[3] && !req[2] && !req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[3] && $past(arb_type == 3'd0)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0])) iff ((gnt[3] && arb_type == 3'b000) |-> (req[3] && !req[2] && !req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] && arb_type == 4'b0000) |->      (req[0] && !req[1])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] && $past(arb_type == 3'd1)) |-> $past(req[0] & ~req[1])) iff ((gnt[0] && arb_type == 4'b0000) |->      (req[0] && !req[1])));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] ##1 (arb_type == 3'b001 |-> req[1])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] && $past(arb_type == 3'd1)) |-> $past(req[1])) iff (gnt[1] ##1 (arb_type == 3'b001 |-> req[1])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] && arb_type == 3'b001)      |->      (req[2] throughout [1:1] && !(req[0] || req[1]))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] && $past(arb_type == 3'd1)) |-> $past(req[2] & ~req[1] & ~req[0])) iff ((gnt[2] && arb_type == 3'b001)      |->      (req[2] throughout [1:1] && !(req[0] || req[1]))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[3] == 1 && arb_type == 3'b0011) |->    (req[3] === 1 && req[2] === 0 && req[1] === 0 && req[0] === 0)));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[3] && $past(arb_type == 3'd1)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0])) iff ((gnt[3] == 1 && arb_type == 3'b0011) |->    (req[3] === 1 && req[2] === 0 && req[1] === 0 && req[0] === 0)));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] && $past(arb_type) == 3'd2) |->    ($past(req[0]) && !$past(req[2]))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] && $past(arb_type == 3'd2)) |-> $past(req[0] & ~req[2])) iff ((gnt[0] && $past(arb_type) == 3'd2) |->    ($past(req[0]) && !$past(req[2]))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] && arb_type == 3'b010) |->      (req[1] throughout (req[0] == 1'b0 && req[2] == 1'b0))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] && $past(arb_type == 3'd2)) |-> $past(req[1] & ~req[2] & ~req[0])) iff ((gnt[1] && arb_type == 3'b010) |->      (req[1] throughout (req[0] == 1'b0 && req[2] == 1'b0))));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && (arb_type == 3'b010) |-> req[2]));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] && $past(arb_type == 3'd2)) |-> $past(req[2])) iff (gnt[2] && (arb_type == 3'b010) |-> req[2]));
assert property (@(posedge clk) disable iff (~rst_n) ((r_gnt[3] && arb_type == 3) |->      (req[3] && !req[2] && !req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[3] && $past(arb_type == 3'd2)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0])) iff ((r_gnt[3] && arb_type == 3) |->      (req[3] && !req[2] && !req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] == 1'b1 && arb_type == 3'b011) |->      (req[0] == 1'b1 && req[3] == 1'b0)));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[0] && $past(arb_type == 3'd3)) |-> $past(req[0] & ~req[3])) iff ((gnt[0] == 1'b1 && arb_type == 3'b011) |->      (req[0] == 1'b1 && req[3] == 1'b0)));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] == 1) &&      (arb_type == 3) |->      (($past(req[1]) == 1) &&      (req[0] == 0) &&      (req[3] == 0))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[1] && $past(arb_type == 3'd3)) |-> $past(req[1] & ~req[3] & ~req[0])) iff ((gnt[1] == 1) &&      (arb_type == 3) |->      (($past(req[1]) == 1) &&      (req[0] == 0) &&      (req[3] == 0))));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] && arb_type == 3) |->    (req[2] && !req[3] && !req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[2] && $past(arb_type == 3'd3)) |-> $past(req[2] & ~req[3] & ~req[0] & ~req[1])) iff ((gnt[2] && arb_type == 3) |->    (req[2] && !req[3] && !req[1] && !req[0])));
assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && (arb_type == 3) |-> req[3]));
assert property (@(posedge clk) disable iff (~rst_n) ((gnt[3] && $past(arb_type == 3'd3)) |-> $past(req[3])) iff (gnt[3] && (arb_type == 3) |-> req[3]));

endmodule
