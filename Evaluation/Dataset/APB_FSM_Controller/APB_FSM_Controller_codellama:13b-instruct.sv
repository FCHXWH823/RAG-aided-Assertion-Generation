// AHB to APG Bridge | Maven Silicon
//
//
//
// APB FSM Controller
// Date:08-06-2022
//
// By-Prajwal Kumar Sahu

module APB_FSM_Controller( Hclk,Hresetn,valid,Haddr1,Haddr2,Hwdata1,Hwdata2,Prdata,Hwrite,Haddr,Hwdata,Hwritereg,tempselx, 
			   Pwrite,Penable,Pselx,Paddr,Pwdata,Hreadyout);

input Hclk,Hresetn,valid,Hwrite,Hwritereg;
input [31:0] Hwdata,Haddr,Haddr1,Haddr2,Hwdata1,Hwdata2,Prdata;
input [2:0] tempselx;
output reg Pwrite,Penable;
output reg Hreadyout;  
output reg [2:0] Pselx;
output reg [31:0] Paddr,Pwdata;

//////////////////////////////////////////////////////PARAMETERS

parameter ST_IDLE=3'b000;
parameter ST_WWAIT=3'b001;
parameter ST_READ= 3'b010;
parameter ST_WRITE=3'b011;
parameter ST_WRITEP=3'b100;
parameter ST_RENABLE=3'b101;
parameter ST_WENABLE=3'b110;
parameter ST_WENABLEP=3'b111;


//////////////////////////////////////////////////// PRESENT STATE LOGIC

reg [2:0] PRESENT_STATE,NEXT_STATE;

always @(posedge Hclk)
 begin:PRESENT_STATE_LOGIC
  if (~Hresetn)
    PRESENT_STATE<=ST_IDLE;
  else
    PRESENT_STATE<=NEXT_STATE;
 end


/////////////////////////////////////////////////////// NEXT STATE LOGIC

always @(PRESENT_STATE,valid,Hwrite,Hwritereg)
 begin:NEXT_STATE_LOGIC
  case (PRESENT_STATE)
    
 	ST_IDLE:begin
		 if (~valid)
		  NEXT_STATE=ST_IDLE;
		 else if (valid && Hwrite)
		  NEXT_STATE=ST_WWAIT;
		 else 
		  NEXT_STATE=ST_READ;
		end    

	ST_WWAIT:begin
		 if (~valid)
		  NEXT_STATE=ST_WRITE;
		 else
		  NEXT_STATE=ST_WRITEP;
		end

	ST_READ: begin
		   NEXT_STATE=ST_RENABLE;
		 end

	ST_WRITE:begin
		  if (~valid)
		   NEXT_STATE=ST_WENABLE;
		  else
		   NEXT_STATE=ST_WENABLEP;
		 end

	ST_WRITEP:begin
		   NEXT_STATE=ST_WENABLEP;
		  end

	ST_RENABLE:begin
		     if (~valid)
		      NEXT_STATE=ST_IDLE;
		     else if (valid && Hwrite)
		      NEXT_STATE=ST_WWAIT;
		     else
		      NEXT_STATE=ST_READ;
		   end

	ST_WENABLE:begin
		     if (~valid)
		      NEXT_STATE=ST_IDLE;
		     else if (valid && Hwrite)
		      NEXT_STATE=ST_WWAIT;
		     else
		      NEXT_STATE=ST_READ;
		   end

	ST_WENABLEP:begin
		      if (~valid && Hwritereg)
		       NEXT_STATE=ST_WRITE;
		      else if (valid && Hwritereg)
		       NEXT_STATE=ST_WRITEP;
		      else
		       NEXT_STATE=ST_READ;
		    end

	default: begin
		   NEXT_STATE=ST_IDLE;
		  end
  endcase
 end


////////////////////////////////////////////////////////OUTPUT LOGIC:COMBINATIONAL

reg Penable_temp,Hreadyout_temp,Pwrite_temp;
reg [2:0] Pselx_temp;
reg [31:0] Paddr_temp, Pwdata_temp;

always @(*)
 begin:OUTPUT_COMBINATIONAL_LOGIC
   case(PRESENT_STATE)
    
	ST_IDLE: begin
			  if (valid && ~Hwrite) 
			   begin:IDLE_TO_READ
			        Paddr_temp=Haddr;
				Pwrite_temp=Hwrite;
				Pselx_temp=tempselx;
				Penable_temp=0;
				Hreadyout_temp=0;
			   end
			  
			  else if (valid && Hwrite)
			   begin:IDLE_TO_WWAIT
			        Pselx_temp=0;
				Penable_temp=0;
				Hreadyout_temp=1;			   
			   end
			   
			  else
                            begin:IDLE_TO_IDLE
			        Pselx_temp=0;
				Penable_temp=0;
				Hreadyout_temp=1;	
			   end
		     end    

	ST_WWAIT:begin
	          if (~valid) 
			   begin:WAIT_TO_WRITE
			    Paddr_temp=Haddr1;
				Pwrite_temp=1;
				Pselx_temp=tempselx;
				Penable_temp=0;
				Pwdata_temp=Hwdata;
				Hreadyout_temp=0;
			   end
			  
			  else 
			   begin:WAIT_TO_WRITEP
			    Paddr_temp=Haddr1;
				Pwrite_temp=1;
				Pselx_temp=tempselx;
				Pwdata_temp=Hwdata;
				Penable_temp=0;
				Hreadyout_temp=0;		   
			   end
			   
		     end  

	ST_READ: begin:READ_TO_RENABLE
			  Penable_temp=1;
			  Hreadyout_temp=1;
		     end

	ST_WRITE:begin
              if (~valid) 
			   begin:WRITE_TO_WENABLE
				Penable_temp=1;
				Hreadyout_temp=1;
			   end
			  
			  else 
			   begin:WRITE_TO_WENABLEP ///DOUBT
				Penable_temp=1;
				Hreadyout_temp=1;		   
			   end
		     end

	ST_WRITEP:begin:WRITEP_TO_WENABLEP
               Penable_temp=1;
			   Hreadyout_temp=1;
		      end

	ST_RENABLE:begin
	            if (valid && ~Hwrite) 
				 begin:RENABLE_TO_READ
					Paddr_temp=Haddr;
					Pwrite_temp=Hwrite;
					Pselx_temp=tempselx;
					Penable_temp=0;
					Hreadyout_temp=0;
				 end
			  
			  else if (valid && Hwrite)
			    begin:RENABLE_TO_WWAIT
			     Pselx_temp=0;
				 Penable_temp=0;
				 Hreadyout_temp=1;			   
			    end
			   
			  else
                begin:RENABLE_TO_IDLE
			     Pselx_temp=0;
				 Penable_temp=0;
				 Hreadyout_temp=1;	
			    end

		       end

	ST_WENABLEP:begin
                 if (~valid && Hwritereg) 
			      begin:WENABLEP_TO_WRITEP
			       Paddr_temp=Haddr2;
				   Pwrite_temp=Hwrite;
				   Pselx_temp=tempselx;
				   Penable_temp=0;
				   Pwdata_temp=Hwdata;
				   Hreadyout_temp=0;
				  end

			  
			    else 
			     begin:WENABLEP_TO_WRITE_OR_READ /////DOUBT
			      Paddr_temp=Haddr2;
				  Pwrite_temp=Hwrite;
				  Pselx_temp=tempselx;
				  Pwdata_temp=Hwdata;
				  Penable_temp=0;
				  Hreadyout_temp=0;		   
			     end
		        end

	ST_WENABLE :begin
	             if (~valid && Hwritereg) 
			      begin:WENABLE_TO_IDLE
				   Pselx_temp=0;
				   Penable_temp=0;
				   Hreadyout_temp=0;
				  end

			  
			    else 
			     begin:WENABLE_TO_WAIT_OR_READ /////DOUBT
				  Pselx_temp=0;
				  Penable_temp=0;
				  Hreadyout_temp=0;		   
			     end

		        end

 endcase
end


////////////////////////////////////////////////////////OUTPUT LOGIC:SEQUENTIAL

always @(posedge Hclk)
 begin
  
  if (~Hresetn)
   begin
    Paddr<=0;
	Pwrite<=0;
	Pselx<=0;
	Pwdata<=0;
	Penable<=0;
	Hreadyout<=0;
   end
  
  else
   begin
        Paddr<=Paddr_temp;
	Pwrite<=Pwrite_temp;
	Pselx<=Pselx_temp;
	Pwdata<=Pwdata_temp;
	Penable<=Penable_temp;
	Hreadyout<=Hreadyout_temp;
   end
 end
 ///////////////////////



assert property(@(posedge Hclk) disable iff (!Hresetn) 1 |-> ##2 PRESENT_STATE == $past(NEXT_STATE));
assert property(@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_IDLE && valid && Hwrite) |-> (NEXT_STATE == ST_WWAIT));
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_IDLE && valid && !Hwrite |-> NEXT_STATE == ST_READ);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_IDLE && !valid |-> NEXT_STATE == ST_IDLE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WWAIT && !valid |-> NEXT_STATE == ST_WRITE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WWAIT && valid |-> NEXT_STATE == ST_WRITEP);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_READ |-> NEXT_STATE == ST_RENABLE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WRITE && !valid |-> NEXT_STATE == ST_WENABLE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WRITE && valid |-> NEXT_STATE == ST_WENABLEP);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WRITEP |-> NEXT_STATE == ST_WENABLEP);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_RENABLE && !valid |-> NEXT_STATE == ST_IDLE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_RENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_RENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLE && !valid |-> NEXT_STATE == ST_IDLE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLEP && !valid && Hwritereg |-> NEXT_STATE == ST_WRITE);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLEP && valid && Hwritereg |-> NEXT_STATE == ST_WRITEP);
assert property(@(posedge Hclk) disable iff (!Hresetn) PRESENT_STATE == ST_WENABLEP && !Hwritereg |-> NEXT_STATE == ST_READ);

assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == NEXT_STATE));
assert property (@(posedge Hclk) disable iff (!Hresetn) (1 |-> ##2 PRESENT_STATE == $past(NEXT_STATE)) iff (PRESENT_STATE == NEXT_STATE));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff (PREVIOUS_STATE == ST_IDLE && TRANSACTION_VALID && TRANSACTION_WRITE));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PRESENT_STATE == ST_IDLE && valid && Hwrite) |-> (NEXT_STATE == ST_WWAIT)) iff (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff (PREVIOUS_STATE == ST_IDLE && TRANSACTION_VALID && TRANSACTION_WRITE));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((valid && !write && state==ST_IDLE) |=> (state==ST_READ)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_IDLE && valid && !Hwrite |-> NEXT_STATE == ST_READ) iff ((valid && !write && state==ST_IDLE) |=> (state==ST_READ)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition) disable iff(...));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_IDLE && !valid |-> NEXT_STATE == ST_IDLE) iff (ONLY logical expression WITHOUT clock signal condition) disable iff(...));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff (current_state == ST_WWAIT && !valid_transaction));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WWAIT && !valid |-> NEXT_STATE == ST_WRITE) iff (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff (current_state == ST_WWAIT && !valid_transaction));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(CURRENT_STATE == ST_WWAIT && VALID_TRANSACTION)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WWAIT && valid |-> NEXT_STATE == ST_WRITEP) iff (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(CURRENT_STATE == ST_WWAIT && VALID_TRANSACTION)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PRESENT_STATE == ST_READ) |-> (NEXT_STATE == ST_READ_ENABLE)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_READ |-> NEXT_STATE == ST_RENABLE) iff ((PRESENT_STATE == ST_READ) |-> (NEXT_STATE == ST_READ_ENABLE)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PREV_ST == ST_WRITE) && (!VALID_TRANSACTION) |-> (NEXT_ST == ST_WRITE)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WRITE && !valid |-> NEXT_STATE == ST_WENABLE) iff ((PREV_ST == ST_WRITE) && (!VALID_TRANSACTION) |-> (NEXT_ST == ST_WRITE)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((STATE == ST_WRITE && TRANSACTION_VALID) |-> NEXT_STATE == ST_WRITE_ENABLE));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WRITE && valid |-> NEXT_STATE == ST_WENABLEP) iff ((STATE == ST_WRITE && TRANSACTION_VALID) |-> NEXT_STATE == ST_WRITE_ENABLE));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PREVIOUS_HOLD(current_state == ST_WRITEP) |-> NEXT_STATE(FSM, ST_WRITEENABLEPIPELINED)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WRITEP |-> NEXT_STATE == ST_WENABLEP) iff (PREVIOUS_HOLD(current_state == ST_WRITEP) |-> NEXT_STATE(FSM, ST_WRITEENABLEPIPELINED)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(PRESENT_STATE == ST_RENABLE && !transaction)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_RENABLE && !valid |-> NEXT_STATE == ST_IDLE) iff (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(PRESENT_STATE == ST_RENABLE && !transaction)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition) disable iff ((state == ST_RENABLE) && valid_trans && write_op));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_RENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT) iff (ONLY logical expression WITHOUT clock signal condition) disable iff ((state == ST_RENABLE) && valid_trans && write_op));
assert property (@(posedge Hclk) disable iff (!Hresetn) (valid && !write && currentState == ST_RENABLE |-> nextState == ST_READ));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_RENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ) iff (valid && !write && currentState == ST_RENABLE |-> nextState == ST_READ));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY (PREV_STATE == ST_WENABLE) && !TRN));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLE && !valid |-> NEXT_STATE == ST_IDLE) iff (ONLY (PREV_STATE == ST_WENABLE) && !TRN));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PREV_ST == ST_WENABLE && TRANS_VALID && PREV_WRITE == 1) |=> (NEXT_ST == ST_WWAIT)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT) iff ((PREV_ST == ST_WENABLE && TRANS_VALID && PREV_WRITE == 1) |=> (NEXT_ST == ST_WWAIT)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((ST_WENABLE && TransactionValid && !WriteOperationActive) |-> (NextState == ST_READ)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ) iff ((ST_WENABLE && TransactionValid && !WriteOperationActive) |-> (NextState == ST_READ)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PREVIOUS_ST_EQ_ST_WENABLEP && !VALID && WRITE_REGISTER_CONTROL) |-> NEXT_ST_EQ_WRITE));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLEP && !valid && Hwritereg |-> NEXT_STATE == ST_WRITE) iff ((PREVIOUS_ST_EQ_ST_WENABLEP && !VALID && WRITE_REGISTER_CONTROL) |-> NEXT_ST_EQ_WRITE));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PRESENT_STATE == ST_WENABLEP && VALID && WRITE_REGISTER_CONTROL_ACTIVE) |=> (NEXT_STATE == ST_WRITEPIPELINED)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLEP && valid && Hwritereg |-> NEXT_STATE == ST_WRITEP) iff ((PRESENT_STATE == ST_WENABLEP && VALID && WRITE_REGISTER_CONTROL_ACTIVE) |=> (NEXT_STATE == ST_WRITEPIPELINED)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PRESENT_STATE == ST_WENABLEP && !WRITE_REGISTER_CONTROL_ACTIVE) |-> (NEXT_STATE == READ)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLEP && !Hwritereg |-> NEXT_STATE == ST_READ) iff ((PRESENT_STATE == ST_WENABLEP && !WRITE_REGISTER_CONTROL_ACTIVE) |-> (NEXT_STATE == READ)));

endmodule
