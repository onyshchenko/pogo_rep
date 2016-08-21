from geopy.distance import VincentyDistance, vincenty
import time
from time import sleep


class MyFunctions():
    def __init__( self):
        self.listOfItems = dict()
        self.map_cells = {}
        self.nearby_forts = {}

    def displayList( self):
        """Prints all items in listOfItems)"""
        print ("displayList")
        print (self.map_cells)
        for item in self.map_cells:
            print item

    def addToList(self):
        """Updates all mlb scores, and places results in a variable."""
        print ("addToList")
        self.map_cells = {'Name': 'Zara', 'Age': 7, 'Name2': 'Manni'};
        test = self.map_cells
        test.update({self.map_cells,12}) 
        #self.map_cells.update({'sdgfsfg': 'sdfgZara'}) 
        #self.map_cells.append("test")

f = MyFunctions()
#f.displayList()
#f.addToList()
#f.displayList()

#near_fort = [{'last_modified_timestamp_ms': 1471348086825L, 'enabled': True, 'longitude': 30.346832, 'latitude': 50.281982, 'type': 1, 'id': u'9fcf7d596c1c46b0b86cded933b6f132.16'}, {'last_modified_timestamp_ms': 1467338156329L, 'enabled': True, 'longitude': 30.34095, 'latitude': 50.271207, 'type': 1, 'id': u'62175c81de5d403b8f6b21c67fc3a0d3.16'}]
#print ("near_fort: ", near_fort)

#near_fort = [(fort, round(vincenty((50.281131, 30.345966), (fort['latitude'], fort['longitude'])).meters)) for fort in near_fort if fort.get('type', None) == 1]
#print ("near_fort: ", near_fort)
#sorted_forts = sorted(near_fort, lambda x, y: cmp(x[1], y[1]))
#print("sorted_forts: ", sorted_forts)

finished_forts = []
#print ("finished_forts", finished_forts)
finished_forts = [{'fort_id': 1534534534534L,'spinned_time': int(round(time.time()))}]
#print ("finished_forts", finished_forts)
sleep(1)
finished_forts.append({'fort_id': 2534534534534L,'spinned_time': int(round(time.time()))})
#print ("finished_forts", finished_forts)
sleep(1)
finished_forts.append({'fort_id': 3534534534534L,'spinned_time': int(round(time.time()))})
print ("finished_forts", finished_forts)

y = 0
for x in finished_forts:
    #print ("x= ", x)
    fff = x['fort_id']
    #print ("fff = ", fff)
    now = int(round(time.time()))
    #print ("now: ", now)
    #print (x.get('spinned_time'))
    if x['spinned_time'] < (now - 1):
        print ("delete this:", x['fort_id'])
        finished_forts.pop(y)
    y += 1

print ("finished_forts", finished_forts)