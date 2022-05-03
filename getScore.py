from math import inf
from urllib.request import urlopen
from bs4 import BeautifulSoup as bs

def getTable(table, team):
	res = []
	teamIdx = -1
	allrows = table.findAll('tr')
	for i in range(0, len(allrows)):
		list = []
		for col in allrows[i].findAll('td'):
			str = [s.strip().replace(',', '') for s in col.findAll(text=True) if s.strip()]
			list.append(str[0])
		if list and list[0] == team: 
			teamIdx = i-1
		res.append(list[4:])
	res.pop(0)
	return res, teamIdx

def bestScore(table):
	ERROR = {'IE', 'TLE', 'WA', 'RTE', 'MLE', 'OLE', 'PLE'}
	nCol = len(table[0])
	best = [inf] * nCol
	for row in table:
		for j in range(0, nCol):
			if row[j] not in ERROR: 
				best[j] = min(best[j], (float(row[j])))
	return best

def teamScore(table, teamIdx):
	ERROR = {'IE', 'TLE', 'WA', 'RTE', 'MLE', 'OLE', 'PLE'}
	score = []
	for val in table[teamIdx]:
		if val in ERROR:
			score.append(val)
		else:
			score.append((float(val)))
	return score

def main():
	# EXACT-LITE: 3195
	# HEURISTIC-LITE: 3196
	# EXACT: 3197
	# HEURISTIC: 3198
	PROBLEM_ID = 3198
	URL = f'https://www.optil.io/optilion/problem/{PROBLEM_ID}/standing'
	USER_NAME = 'convo'

	soup = bs(urlopen(URL), 'html.parser')
	table, teamIdx = getTable(soup.find('table'), USER_NAME)
	best = bestScore(table)
	team = teamScore(table, teamIdx)
	
	with open('output', 'w') as f:
		for i in range(0, len(best)):
			print(i+1, best[i], team[i], file=f)

if __name__ == "__main__":
	main()
