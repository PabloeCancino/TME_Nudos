import requests

url = "https://knotinfo.org/results.php?searchmode=singleknot&desktopmode=0&mobilemode=0&singleknotprev=&submittype=singleknot&singleknot=3_1"
try:
    response = requests.get(url)
    response.raise_for_status()
    with open("knotinfo_sample.html", "w", encoding="utf-8") as f:
        f.write(response.text)
    print("HTML saved to knotinfo_sample.html")
except Exception as e:
    print(f"Error: {e}")
