import PyPDF2
import sys
import os

# Use raw string for the path to handle backslashes and special characters
pdf_path = r"E:\Nudos - Propuesta de Formalizacion racional\liang1995.pdf"

print(f"Attempting to read: {pdf_path}")

if not os.path.exists(pdf_path):
    print("Error: File not found.")
    sys.exit(1)

try:
    with open(pdf_path, 'rb') as pdf_file:
        reader = PyPDF2.PdfReader(pdf_file)
        num_pages = len(reader.pages)
        print(f"Total Pages: {num_pages}")
        
        # Read first 20 pages to get Chapter VII content
        for i in range(min(20, num_pages)):
            try:
                text = reader.pages[i].extract_text()
                print(f"\n--- PAGE {i+1} ---\n")
                print(text)
                print("\n" + "=" * 80)
            except Exception as e:
                print(f"Error extracting page {i+1}: {e}")
            
except Exception as e:
    print(f"Error reading PDF: {e}")
    sys.exit(1)
