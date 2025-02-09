import faiss
import numpy as np
# Load the FAISS index
index = faiss.read_index("RAG_Database/Book1-CernyDudani-SVA- The Power of Assertions in SystemVerilog/index.faiss")

# Print basic information
print("Number of vectors:", index.ntotal)
print("Vector dimension:", index.d)

# Retrieve the first 5 stored vectors (if they exist)
num_vectors_to_fetch = min(5, index.ntotal)  # Fetch at most 5 vectors
vectors = [index.reconstruct(i) for i in range(num_vectors_to_fetch)]
d = index.d
query_vector = np.random.rand(1, d).astype('float32')

# Search for the 5 nearest neighbors
k = 5
distances, indices = index.search(query_vector, k)

print("Nearest neighbor indices:", indices)
print("Distances:", distances)
