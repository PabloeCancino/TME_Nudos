import requests
from bs4 import BeautifulSoup
import json
import time
import sys
BASE_URL = "https://knotinfo.org/results.php?searchmode=singleknot&desktopmode=0&mobilemode=0&singleknotprev=&submittype=singleknot&singleknot={}"
def get_knot_ids():
    """Generates Rolfsen knot IDs from 3_1 to 10_166."""
    knots = []
    # 3 to 9 crossings
    limits = {
        3: 1, 4: 1, 5: 2, 6: 3, 7: 7, 8: 21, 9: 49, 10: 166
    }
    
    for n in range(3, 11):
        limit = limits[n]
        for i in range(1, limit + 1):
            knots.append(f"{n}_{i}")
            
    return knots
def scrape_knot(knot_id):
    url = BASE_URL.format(knot_id)
    try:
        response = requests.get(url, timeout=10)
        response.raise_for_status()
        
        soup = BeautifulSoup(response.text, 'html.parser')
        table = soup.find('table')
        
        if not table:
            print(f"Warning: No table found for {knot_id}")
            return None
            
        data = {"id": knot_id}
        
        for row in table.find_all('tr'):
            cols = row.find_all('td')
            if len(cols) == 2:
                key = cols[0].text.strip().rstrip(':')
                # Get text, but also check for links if needed. 
                # For now, text is usually sufficient, but some fields like 'a_polynomial' might be a link.
                # The user said "all info provided", so text is the safest general representation.
                value = cols[1].text.strip()
                data[key] = value
                
        return data
    except Exception as e:
        print(f"Error scraping {knot_id}: {e}")
        return None
def main():
    knots = get_knot_ids()
    total = len(knots)
    results = []
    
    print(f"Starting scrape for {total} knots...")
    
    for i, knot_id in enumerate(knots):
        print(f"[{i+1}/{total}] Scraping {knot_id}...", end='\r')
        data = scrape_knot(knot_id)
        if data:
            results.append(data)
        
        # Be polite to the server
        time.sleep(0.2)
        
    print("\nScrape complete.")
    
    with open("DB_knotinfo.json", "w", encoding="utf-8") as f:
        json.dump(results, f, indent=4, ensure_ascii=False)
        
    print(f"Data saved to DB_knotinfo.json ({len(results)} records)")
if __name__ == "__main__":
    main()
