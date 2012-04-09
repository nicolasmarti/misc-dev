import re, urllib

def get_quote(symbol):
    base_url = 'http://finance.google.com/finance?q='
    content = urllib.urlopen(base_url + symbol).read()
    find_q = re.search(r'\<span\sid="ref_\d+.*">(.+)<', content)
    return find_q.group(1) if find_q else 'no quote available for: %s' % symbol

def print_quotes(companys):
    for company in companys:
        print '%s --> %s' %  (company,get_quote(company))

def caca():
    return "pipi"

if __name__ == "__main__":
    #Test of 5 companys
    print_quotes(['google', 'ibm', 'microsoft', 'apple', 'nvidia'])
