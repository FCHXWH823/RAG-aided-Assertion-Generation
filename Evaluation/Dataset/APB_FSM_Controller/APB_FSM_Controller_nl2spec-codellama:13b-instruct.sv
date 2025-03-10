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

assert property (@(posedge Hclk) disable iff (!Hresetn) ((s_eventually (request && $past(grant))) |=> grant));
assert property (@(posedge Hclk) disable iff (!Hresetn) (1 |-> ##2 PRESENT_STATE == $past(NEXT_STATE)) iff ((s_eventually (request && $past(grant))) |=> grant));
assert property (@(posedge Hclk) disable iff (!Hresetn) (translate_sentence(sentence.split() for word in words if word in ["and", "or", "not"] ? {"and": "&&", "or": "||", "not": "!"}[word] : word in ["eventually", "always", "never"] ? {"eventually": "F", "always": "G", "never": "!G"}[word] : word == "last" ? "$past" : word)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((PRESENT_STATE == ST_IDLE && valid && Hwrite) |-> (NEXT_STATE == ST_WWAIT)) iff (translate_sentence(sentence.split() for word in words if word in ["and", "or", "not"] ? {"and": "&&", "or": "||", "not": "!"}[word] : word in ["eventually", "always", "never"] ? {"eventually": "F", "always": "G", "never": "!G"}[word] : word == "last" ? "$past" : word)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ST_IDLE && TRANSACTION_VALID && !WRITE_OPERATION_ACTIVE |=> NEXT_STATE_EQUALS_READ));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_IDLE && valid && !Hwrite |-> NEXT_STATE == ST_READ) iff (ST_IDLE && TRANSACTION_VALID && !WRITE_OPERATION_ACTIVE |=> NEXT_STATE_EQUALS_READ));
assert property (@(posedge Hclk) disable iff (!Hresetn) (translate_sentence(sentence) == "Translate Sentence Sentence Split Sentence Words Initialize Translation Loop Word Check Word Logical Operator Convert Uppercase Check Word Temporal Operator Convert Title Add Word Translation Return Translation Strip"));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_IDLE && !valid |-> NEXT_STATE == ST_IDLE) iff (translate_sentence(sentence) == "Translate Sentence Sentence Split Sentence Words Initialize Translation Loop Word Check Word Logical Operator Convert Uppercase Check Word Temporal Operator Convert Title Add Word Translation Return Translation Strip"));
assert property (@(posedge Hclk) disable iff (!Hresetn) (sentence.split() |-> (foreach (words[i]) ((words[i].endswith("ity") && translated_sentence += "be ") || (words[i].endswith("ness") && translated_sentence += "to be ") || (!words[i].endswith("ity") && !words[i].endswith("ness") && translated_sentence += words[i].title() + " ")))));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WWAIT && !valid |-> NEXT_STATE == ST_WRITE) iff (sentence.split() |-> (foreach (words[i]) ((words[i].endswith("ity") && translated_sentence += "be ") || (words[i].endswith("ness") && translated_sentence += "to be ") || (!words[i].endswith("ity") && !words[i].endswith("ness") && translated_sentence += words[i].title() + " ")))));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (request && $past(grant, 1)) |-> grant));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WWAIT && valid |-> NEXT_STATE == ST_WRITEP) iff (s_eventually (request && $past(grant, 1)) |-> grant));
assert property (@(posedge Hclk) disable iff (!Hresetn) (state == next_state));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_READ |-> NEXT_STATE == ST_RENABLE) iff (state == next_state));
assert property (@(posedge Hclk) disable iff (!Hresetn) (Hstate == ST_WRITE & Hvalid == 0 |=> Hstate' == ST_WRITEENABLE));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WRITE && !valid |-> NEXT_STATE == ST_WENABLE) iff (Hstate == ST_WRITE & Hvalid == 0 |=> Hstate' == ST_WRITEENABLE));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((a && s_eventually b) |=> c && $past(d)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WRITE && valid |-> NEXT_STATE == ST_WENABLEP) iff ((a && s_eventually b) |=> c && $past(d)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (condition1) |=> (condition2 || $past(condition3))));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WRITEP |-> NEXT_STATE == ST_WENABLEP) iff (s_eventually (condition1) |=> (condition2 || $past(condition3))));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (condition_a) ==> $past(condition_b)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_RENABLE && !valid |-> NEXT_STATE == ST_IDLE) iff (s_eventually (condition_a) ==> $past(condition_b)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (translate_sentence(sentence)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_RENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT) iff (translate_sentence(sentence)));
assert property (@(posedge Hclk) disable iff (!Hresetn) ((sentence.split().map(word => word[-1] == "e" ? word + "s" : word + "ed").join(" ").strip()) == translated_sentence));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_RENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ) iff ((sentence.split().map(word => word[-1] == "e" ? word + "s" : word + "ed").join(" ").strip()) == translated_sentence));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (condition) |=> $past(signal)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLE && !valid |-> NEXT_STATE == ST_IDLE) iff (s_eventually (condition) |=> $past(signal)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (out == in)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLE && valid && Hwrite |-> NEXT_STATE == ST_WWAIT) iff (s_eventually (out == in)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (reset == 1) & $past(enable) == 0));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLE && valid && !Hwrite |-> NEXT_STATE == ST_READ) iff (s_eventually (reset == 1) & $past(enable) == 0));
assert property (@(posedge Hclk) disable iff (!Hresetn) (1));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLEP && !valid && Hwritereg |-> NEXT_STATE == ST_WRITE) iff (1));
assert property (@(posedge Hclk) disable iff (!Hresetn) (s_eventually (b |=> $past(a))));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLEP && valid && Hwritereg |-> NEXT_STATE == ST_WRITEP) iff (s_eventually (b |=> $past(a))));
assert property (@(posedge Hclk) disable iff (!Hresetn) (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(...)));
assert property (@(posedge Hclk) disable iff (!Hresetn) (PRESENT_STATE == ST_WENABLEP && !Hwritereg |-> NEXT_STATE == ST_READ) iff (ONLY logical expression WITHOUT clock signal condition @(posedge clock) and WITHOUT disable condition disable iff(...)));

endmodule
