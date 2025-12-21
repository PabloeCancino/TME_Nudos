
with open('crypto_results_7.txt', 'r', encoding='utf-16') as f:
    lines = f.readlines()

print_mode = False
for line in lines:
    if "Nudo 7_" in line:
        print_mode = True
    if "Nudo 8_" in line:
        print_mode = False
        
    if print_mode:
        print(line.strip())
