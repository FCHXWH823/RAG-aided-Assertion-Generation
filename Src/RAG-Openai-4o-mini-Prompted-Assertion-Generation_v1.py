from langchain_community.document_loaders import PyMuPDFLoader
import pandas as pd
import csv
from langchain_openai import OpenAIEmbeddings
from langchain_community.vectorstores import FAISS
import yaml



with open("Src/Config.yml") as file:
    config = yaml.safe_load(file)

PDF_Name = config["PDF_Name"]
Folder_Name = f"Book1-{PDF_Name}"

OpenAI_API_Key = config["Openai_API_Key"]
# Initialize embeddings
embeddings = OpenAIEmbeddings(openai_api_key=OpenAI_API_Key)
vector_store = FAISS.load_local(f"RAG_Database/{Folder_Name}",embeddings,allow_dangerous_deserialization=True)

retriever = vector_store.as_retriever(search_kwargs={'k': 3})

# from langchain.llms import OpenAI
from langchain_openai import ChatOpenAI
from langchain.chains import RetrievalQA

# class LoggingRetrievalQA(RetrievalQA):
#     def run(self, prompt):
#         # Retrieve the relevant documents based on embeddings
#         embedded_query = self.embeddings.embed_text(prompt)
#         search_results, distances = self.vector_store.search(embedded_query, k=3)
        
#         # Log the retrieved texts
#         retrieved_texts = [self.documents[idx] for idx in search_results]
#         for text in retrieved_texts:
#             print("Retrieved Text:", text)
        
#         # Continue with the normal QA process
#         return super().run(prompt)

llm = ChatOpenAI(
    model="gpt-4o-mini-2024-07-18",
    api_key=OpenAI_API_Key
    )

qa_chain = RetrievalQA.from_chain_type(llm, retriever=retriever)


purecode ="""
module fifo_tb1;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty;
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);         
      end

      disable generate_clock;
      $display(""""Tests Completed."""");      
   end // initial begin
   
endmodule
"""

humanexplanation = """
"Assertion 1:
This assertion ensures that a write operation (DUT.valid_wr) cannot occur when the FIFO is full (full). It is checked at every positive edge of the clock (clk).
The assertion should be with the format:
```
always @(posedge clk) begin
      assert(xxxx);     
end 
```

Assertion 2:
This assertion ensures that a read operation (DUT.valid_rd) cannot occur when the FIFO is empty (empty). It is checked at every positive edge of the clock (clk).
The two assertions should be with the format:
```
always @(posedge clk) begin
      assert(xxxx);     
end 
```
Assertion 3:
This assertion is used to check when clk is at posedge, the DUT.valid_wr and full signal can not be 1 at the same time. This assertion should be with the format:
```
assert property (@(posedge clk) xxxx)
```

Assertion 4:
This assertion is used to check when clk is at posedge, the DUT.valid_rd and empty signal can not be 1 at the same time.
This assertion should be with the format:
```
assert property (@(posedge clk) xxxx)
```

Assertion 5:
This assertion is to check when clk is at posedge, if a write operation is valid (DUT.valid_wr) on the current clock edge, then the FIFO should not be full (!full) in th current clock cycle. 
This assertion should be with the format:
```
assert property (@(posedge clk) xxxx)
```

Assertion 6:
This assertion is to check when clk is at posedge, if a read operation is valid (DUT.valid_rd), the FIFO should not be empty (!empty) in the current clock cycle.
This assertion should be with the format:
```
assert property (@(posedge clk) xxxx)
```"
"""

prompt = f"Given Verilog code snippet as below: \n{purecode}\n Please generate a rewritten version of it, which contains several useful assertions and each of them follows a description as follows:{humanexplanation}\n"

llm_response = qa_chain.run(prompt)

retrieved_text = retriever.get_relevant_documents(prompt)

for i, doc in enumerate(retrieved_text):
   print(f"The {i}-th retrieved text:\n {doc.page_content}\n")

print(llm_response)