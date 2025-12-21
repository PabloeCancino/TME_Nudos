import PyPDF2
import sys
import os

# Extract specific page range for Chapter VII
pdf_path = r"E:\Nudos - Propuesta de Formalizacion racional\crowell1977.pdf"

print(f"Attempting to read: {pdf_path}")

if not os.path.exists(pdf_path):
    print("Error: File not found.")
    sys.exit(1)

try:
    with open(pdf_path, 'rb') as pdf_file:
        reader = PyPDF2.PdfReader(pdf_file)
        num_pages = len(reader.pages)
        print(f"Total Pages: {num_pages}")
        
        # Extract Chapter VII: pages 94-110 (approx)
        # PDF pages are 0-indexed, so page 94 in book = index 93
        start_page = 93  # Page 94 in book
        end_page = 110   # Page 111 in book
        
        for i in range(start_page, min(end_page, num_pages)):
            try:
                text = reader.pages[i].extract_text()
                print(f"\n--- PAGE {i+1} (Book page ~{i-5}) ---\n")
                print(text)
                print("\n" + "=" * 80)
            except Exception as e:
                print(f"Error extracting page {i+1}: {e}")
            
except Exception as e:
    print(f"Error reading PDF: {e}")
    sys.exit(1)
