parameter N_MASTERS = 3;
typedef bit [N_MASTERS-1:0] arb_vector;
parameter arb_vector NO_REQUEST = '{default: '0};
parameter arb_vector NO_GRANT = '{default: '0};

module busarbiter(input clk, reset, bus_ack, input arb_vector bus_req, output arb_vector bus_grant);

    enum {READY, BUSY} state_s;
    arb_vector prio_req;
    reg found;
    always @(bus_req) begin: prio
        arb_vector prio_req_v;
	found = 0;
        for (int i=0; i < N_MASTERS; i++) begin
            if(~found & (bus_req[i]==1'b1)) begin
                prio_req_v[i] = 1'b1;
                found = 1;
            end
            else begin
                prio_req_v[i] = 1'b0;
            end
        end
        prio_req <= prio_req_v;
    end

    always @(posedge clk or posedge reset) begin: ctrl
        if(reset) begin //always block triggered by reset
            state_s <= READY;
            bus_grant <= NO_GRANT;
        end
        else begin //always block triggered by clk
            case (state_s)
                READY: begin
                    if (bus_req == NO_REQUEST) begin
			state_s <= READY;
                    end
                    else begin
                        state_s <= BUSY;
                    end 
                    bus_grant <= prio_req;
                end

                BUSY: begin
                    if (bus_ack) begin
                        if (bus_req == NO_REQUEST) begin
                            state_s <= READY;
                        end
                        else begin
                            state_s <= BUSY;
                        end 
		        bus_grant <= prio_req;
		    end
                end
            endcase 
        end
    end

assert property(@(posedge clk)  bus_grant[0]+bus_grant[1]+bus_grant[2]<2);
assert property(@(posedge clk)  bus_grant[0] |-> (!bus_grant[1] && !bus_grant[2]));
assert property(@(posedge clk)  bus_grant[1] |-> (!bus_grant[0] && !bus_grant[2]));
assert property(@(posedge clk)  bus_grant[2] |-> (!bus_grant[1] && !bus_grant[0]));
assert property(@(posedge clk)  bus_grant != NO_GRANT && bus_ack != 1 |=> $stable(bus_grant));
assert property(@(posedge clk)  (bus_req[0] && bus_grant== NO_GRANT)|| (bus_ack && bus_req[0]) |=>  (bus_grant[0] && !bus_grant[1] && !bus_grant[2]));
assert property(@(posedge clk)  (bus_req[1] && !bus_req[0] && bus_grant== NO_GRANT) || (bus_ack && bus_req[1]&& !bus_req[0])|=>  (!bus_grant[0] && bus_grant[1] && !bus_grant[2]));
assert property(@(posedge clk)  (bus_req[2] && !bus_req[1] && !bus_req[0] && bus_grant== NO_GRANT) || (bus_ack && bus_req[2]&& !bus_req[0] &&  !bus_req[1]) |=>  (!bus_grant[0] && !bus_grant[1] && bus_grant[2]));
assert property(@(posedge clk)  $rose(bus_grant[1]) |-> ($past(bus_req[1]) && !$past(bus_req[0])));
assert property(@(posedge clk)  $rose(bus_grant[2]) |-> ($past(bus_req[2]) && !$past(bus_req[1]) && !$past(bus_req[0])));

assert property (@(posedge clk)  (bus_grant[0] + bus_grant[1] + bus_grant[2] < 2));
assert property (@(posedge clk)  (bus_grant[0] + bus_grant[1] + bus_grant[2] < 2) iff (bus_grant[0] + bus_grant[1] + bus_grant[2] < 2));
assert property (@(posedge clk)  (bus_grant[1] |-> (bus_grant[2] == 0) && (bus_grant[3] == 0)));
assert property (@(posedge clk)  (bus_grant[0] |-> (!bus_grant[1] && !bus_grant[2])) iff (bus_grant[1] |-> (bus_grant[2] == 0) && (bus_grant[3] == 0)));
assert property (@(posedge clk)  (bus_grant[1] |=> (bus_grant[0] == 0) && (bus_grant[2] == 0)));
assert property (@(posedge clk)  (bus_grant[1] |-> (!bus_grant[0] && !bus_grant[2])) iff (bus_grant[1] |=> (bus_grant[0] == 0) && (bus_grant[2] == 0)));
assert property (@(posedge clk)  (bus_grant[2] |=> (bus_grant[1] == 0 && bus_grant[0] == 0)));
assert property (@(posedge clk)  (bus_grant[2] |-> (!bus_grant[1] && !bus_grant[0])) iff (bus_grant[2] |=> (bus_grant[1] == 0 && bus_grant[0] == 0)));
assert property (@(posedge clk)  (bus_grant != NO_GRANT && !bus_ack |-> (bus_grant == bus_grant)));
assert property (@(posedge clk)  (bus_grant != NO_GRANT && bus_ack != 1 |=> $stable(bus_grant)) iff (bus_grant != NO_GRANT && !bus_ack |-> (bus_grant == bus_grant)));
assert property (@(posedge clk)  (bus_req[0] && (bus_grant == NO_GRANT) || (bus_ack && bus_req[0]) |-> (bus_grant[0] && !bus_grant[1] && !bus_grant[2])));
assert property (@(posedge clk)  ((bus_req[0] && bus_grant == NO_GRANT) || (bus_ack && bus_req[0]) |=> (bus_grant[0] && !bus_grant[1] && !bus_grant[2])) iff (bus_req[0] && (bus_grant == NO_GRANT) || (bus_ack && bus_req[0]) |-> (bus_grant[0] && !bus_grant[1] && !bus_grant[2])));
assert property (@(posedge clk)  ((bus_req[1] && !bus_req[0] && bus_grant == NO_GRANT) || (bus_ack && bus_req[1] && !bus_req[0]) |-> (bus_grant[1] && !bus_grant[0] && !bus_grant[2])));
assert property (@(posedge clk)  ((bus_req[1] && !bus_req[0] && bus_grant == NO_GRANT) || (bus_ack && bus_req[1] && !bus_req[0]) |=> (!bus_grant[0] && bus_grant[1] && !bus_grant[2])) iff ((bus_req[1] && !bus_req[0] && bus_grant == NO_GRANT) || (bus_ack && bus_req[1] && !bus_req[0]) |-> (bus_grant[1] && !bus_grant[0] && !bus_grant[2])));
assert property (@(posedge clk)  ((bus_req[2] && !bus_req[1] && !bus_req[0] && (bus_grant == NO_GRANT)) || (bus_ack && bus_req[2] && !bus_req[1] && !bus_req[0]) |-> (bus_grant[2] && !bus_grant[1] && !bus_grant[0])));
assert property (@(posedge clk)  ((bus_req[2] && !bus_req[1] && !bus_req[0] && bus_grant == NO_GRANT) || (bus_ack && bus_req[2] && !bus_req[0] && !bus_req[1]) |=> (!bus_grant[0] && !bus_grant[1] && bus_grant[2])) iff ((bus_req[2] && !bus_req[1] && !bus_req[0] && (bus_grant == NO_GRANT)) || (bus_ack && bus_req[2] && !bus_req[1] && !bus_req[0]) |-> (bus_grant[2] && !bus_grant[1] && !bus_grant[0])));
assert property (@(posedge clk)  (bus_grant[1] |=> (bus_req[1] && !bus_req[0])));
assert property (@(posedge clk)  ($rose(bus_grant[1]) |-> ($past(bus_req[1]) && !$past(bus_req[0]))) iff (bus_grant[1] |=> (bus_req[1] && !bus_req[0])));
assert property (@(posedge clk)  (bus_grant[2] |-> (bus_req[2] && !bus_req[1] && !bus_req[0])));
assert property (@(posedge clk)  ($rose(bus_grant[2]) |-> ($past(bus_req[2]) && !$past(bus_req[1]) && !$past(bus_req[0]))) iff (bus_grant[2] |-> (bus_req[2] && !bus_req[1] && !bus_req[0])));

endmodule
