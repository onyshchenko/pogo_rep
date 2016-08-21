# Time to put in proper comments overywher
from __future__ import absolute_import

import logging
# import re
from itertools import chain, imap

# import requests
# from .utilities import f2i
# from termcolor import colored # get color logging soon
from pgoapi.protos.POGOProtos.Networking.Requests_pb2 import RequestType
from pgoapi.protos.POGOProtos import Inventory_pb2 as Inventory
from pgoapi.exceptions import ServerSideRequestThrottlingException

import pickle
import random
import json
import xml.etree.ElementTree as ETXML
from pogobot.location import distance_in_meters, get_increments, get_neighbors, get_route, filtered_forts, append_elevation
# import pgoapi.protos.POGOProtos.Enums_pb2 as RpcEnum
from pogobot.poke_utils import pokemon_iv_percentage, get_inventory_data, get_pokemon_num, get_incubators_stat, incubators_stat_str, \
    get_eggs_stat
from time import sleep
from collections import defaultdict

import sys
import os.path
import platform
import time

from geopy.distance import VincentyDistance, vincenty

from pgoapi import PGoApi
from pgoapi import utilities as util

# Candy needed to evolve pokemon  to add new pokemon to auto evolve list edit them here
CANDY_NEEDED_TO_EVOLVE = {1: 124,  # Bulbasaur
                          2: 99,  # Ivysaur
                          4: 124,  # Charmander
                          5: 99,  # Charmeleon
                          7: 124,  # Squirtle
                          8: 99,  # Wartortle
                          10: 61,  # Caterpie
                          11: 49,  # Metapod
                          13: 61,  # Weedle
                          14: 49,  # Kakuna
                          16: 61,  # Pidgey
                          17: 49,  # Pidgeotto
                          19: 24,  # Rattata
                          21: 49,  # Spearow
                          23: 49,  # Ekans
                          25: 49,
                          27: 49,
                          29: 124,
                          30: 99,
                          32: 124,
                          33: 99,
                          35: 49,
                          37: 49,
                          39: 50,
                          41: 44,
                          43: 124,
                          44: 99,
                          46: 49,
                          48: 49,
                          50: 49,
                          52: 49,
                          54: 49,
                          56: 49,
                          58: 49,
                          60: 124,  # Poliwag
                          61: 99,
                          63: 124,
                          64: 99,
                          66: 124,
                          67: 99,
                          69: 124,
                          70: 99,
                          72: 49,
                          74: 124,
                          75: 99,
                          77: 49,
                          79: 49,
                          81: 49,
                          84: 49,
                          86: 49,
                          88: 49,
                          90: 49,  # Shellder
                          92: 124,
                          93: 99,
                          96: 49,  # Drowzee
                          98: 49,
                          100: 49,
                          102: 49,
                          104: 49,
                          109: 49,
                          111: 49,
                          116: 49,
                          118: 49,
                          120: 49,
                          129: 399,
                          133: 24,
                          138: 49,
                          140: 49,
                          147: 124,
                          148: 99}

POKEBALLS = ["Pokeball", "Great Ball", "Ultra Ball", "Master Ball"]  # you only get one master ball dont waste it botting

MIN_SIMILAR_POKEMON = 1  # change this to keep more doubles if you have release duplicates set to ture

INVENTORY_DICT = {Inventory.ITEM_UNKNOWN: "UNKNOWN",
                  Inventory.ITEM_POKE_BALL: "POKE_BALL",
                  Inventory.ITEM_GREAT_BALL: "GREAT_BALL",
                  Inventory.ITEM_ULTRA_BALL: "ULTRA_BALL",
                  Inventory.ITEM_MASTER_BALL: "MASTER_BALL",
                  Inventory.ITEM_POTION: "POTION",
                  Inventory.ITEM_SUPER_POTION: "SUPER_POTION",
                  Inventory.ITEM_HYPER_POTION: "HYPER_POTION",
                  Inventory.ITEM_MAX_POTION: "MAX_POTION",
                  Inventory.ITEM_REVIVE: "REVIVE",
                  Inventory.ITEM_MAX_REVIVE: "MAX_REVIVE",
                  Inventory.ITEM_LUCKY_EGG: "LUCKY_EGG",
                  Inventory.ITEM_INCENSE_ORDINARY: "INCENSE_ORDINARY",
                  Inventory.ITEM_INCENSE_SPICY: "INCENSE_SPICY",
                  Inventory.ITEM_INCENSE_COOL: "INCENSE_COOL",
                  Inventory.ITEM_INCENSE_FLORAL: "INCENSE_FLORAL",
                  Inventory.ITEM_TROY_DISK: "TROY_DISK/LURE_MODULE",
                  Inventory.ITEM_X_ATTACK: "X_ATTACK",
                  Inventory.ITEM_X_DEFENSE: "X_DEFENSE",
                  Inventory.ITEM_X_MIRACLE: "X_MIRACLE",
                  Inventory.ITEM_RAZZ_BERRY: "RAZZ_BERRY",
                  Inventory.ITEM_BLUK_BERRY: "BLUK_BERRY",
                  Inventory.ITEM_NANAB_BERRY: "NANAB_BERRY",
                  Inventory.ITEM_WEPAR_BERRY: "WEPAR_BERRY",
                  Inventory.ITEM_PINAP_BERRY: "PINAP_BERRY",
                  Inventory.ITEM_SPECIAL_CAMERA: "SPECIAL_CAMERA",
                  Inventory.ITEM_INCUBATOR_BASIC_UNLIMITED: "INCUBATOR_BASIC_UNLIMITED",
                  Inventory.ITEM_INCUBATOR_BASIC: "INCUBATOR_BASIC",
                  Inventory.ITEM_POKEMON_STORAGE_UPGRADE: "POKEMON_STORAGE_UPGRADE",
                  Inventory.ITEM_ITEM_STORAGE_UPGRADE: "ITEM_STORAGE_UPGRADE"}


class PoGObot:

    def __init__(self, config, pokemon_names, start_pos):

        self.api = PGoApi()
        self.log = logging.getLogger(__name__)
        self._start_pos = start_pos
        self._posf = start_pos
        self._walk_count = 1
        self.first_fort = {}
        self.config = config
        self.evolved_pokemon_ids = []
        self.GPX_lat = []
        self.GPX_lon = []
        self._pokeball_type = 1
        self.GMAPS_KEY = config.get("GMAPS_API_KEY", "")
        self.MIN_KEEP_IV = config.get("MIN_KEEP_IV", 0)
        self.KEEP_CP_OVER = config.get("KEEP_CP_OVER", 0)
        self.RELEASE_DUPLICATES = config.get("RELEASE_DUPLICATE", 0)
        self.DUPLICATE_CP_FORGIVENESS = config.get("DUPLICATE_CP_FORGIVENESS", 0)
        self.MAX_BALL_TYPE = config.get("MAX_BALL_TYPE", 0)
        self.SLOW_BUT_STEALTH = config.get("SLOW_BUT_STEALTH", 0)
        self.AUTO_HATCHING = config.get("AUTO_HATCHING", False)
        self._req_method_list = []
        self._heartbeat_number = 0
        self.pokemon_names = pokemon_names
        self.pokeballs = [0, 0, 0, 0]  # pokeball counts. set to 0 to force atleast one fort check  before trying to capture pokemon
        self.map_cells = dict()
        self.map_cells_w = dict()
        self.walk_fort_id = 0
        self.finished_forts = {}
        #self.nearby_forts = {}
        #self.nearby_pokemons = {}
        self.last_map_request = ({'time': 0, 'latitude': 0, 'longitude': 0})
        self.min_item_counts = dict(
            ((getattr(Inventory, key), value) for key, value in config.get('MIN_ITEM_COUNTS', {}).iteritems())
        )

    def response_parser(self, res):
        if os.path.isfile("accounts/%s/Inventory.json" % self.config['username']) and 'GET_INVENTORY' in res['responses']:
            with open("accounts/%s/Inventory.json" % self.config['username'], "w") as file_to_write:
                file_to_write.write(json.dumps(res['responses'], indent=2))
                file_to_write.close()
            with open("accounts/%s/Inventory.json" % self.config['username'], "r") as file_to_read:
                file = file_to_read.read()
                json_file = json.loads(file)
        if 'GET_PLAYER' in res['responses']:
            if os.path.isfile("accounts/%s/Player.json" % self.config['username']):
                with open("accounts/%s/Player.json" % self.config['username'], "w") as file_to_write:
                    file_to_write.write(json.dumps(res['responses'], indent=2))
                    file_to_write.close()
            player_data = res['responses'].get('GET_PLAYER', {}).get('player_data', {})
            print ("player_data: ", player_data)
            self.log.info('Player_data: \n\r{}'.format(json.dumps(player_data, indent=2)))
            inventory_items = json_file.get('GET_INVENTORY', {}).get('inventory_delta', {}).get('inventory_items', [])
            inventory_items_dict_list = map(lambda x: x.get('inventory_item_data', {}), inventory_items)
            player_stats = filter(lambda x: 'player_stats' in x, inventory_items_dict_list)[0].get('player_stats', {})
            currencies = player_data.get('currencies', [])
            currency_data = ",".join(map(lambda x: "{0}: {1}".format(x.get('name', 'NA'), x.get('amount', 'NA')), currencies))
            self.log.info("\n\n Username: %s, Lvl: %s, XP: %s/%s \n Currencies: %s \n", player_data.get('username', 'NA'), player_stats.get('level', 'NA'), player_stats.get('experience', 'NA'), player_stats.get('next_level_xp', 'NA'), currency_data)
        if 'GET_INVENTORY' in res['responses']:
            res['responses']['lat'] = self._posf[0]
            res['responses']['lng'] = self._posf[1]
            self.log.info("\n\nList of Pokemon:\n" + get_inventory_data(res, self.pokemon_names) + "\nTotal Pokemon count: " + str(get_pokemon_num(res)) + "\n\nEgg Hatching status: " + incubators_stat_str(res) + "\n")
            self.log.info("Cleaning up inventory")
            self.cleanup_inventory(res['responses']['GET_INVENTORY']['inventory_delta']['inventory_items'])
            # new inventory data has just been saved, clearing evolved pokemons list
            self.evolved_pokemon_ids = []
        if 'GET_MAP_OBJECTS' in res['responses']:
            if os.path.isfile("accounts/%s/Map.json" % self.config['username']):
                with open("accounts/%s/Map.json" % self.config['username'], "w") as file_to_write:
                    file_to_write.write(json.dumps(res['responses'], indent=2))
                    file_to_write.close()
        return

    def heartbeat(self):
        res = self.api.get_inventory()
        sleep(2 * random.random() + 5)
        self.log.debug('Heartbeat dictionary: \n\r{}'.format(json.dumps(res, indent=2)))
        self.response_parser(res=res)
        if self.AUTO_HATCHING and self._heartbeat_number % 10 == 0:
            hatching_eggs_count = self.attempt_hatch_eggs(res=res)
            if hatching_eggs_count > 0:
                self.log.info("Start hatching %d eggs", hatching_eggs_count)
        #self.spin_near_fort()
        self._heartbeat_number += 1
        return res

    def walk_to(self, loc):
        self._walk_count += 1
        steps = get_route(self._posf, loc, self.GMAPS_KEY)
        #print ("steps", steps)
        for step in steps:
            for next_point in enumerate(get_increments(self._posf, step, self.config.get("STEP_SIZE", 70))):
                final_point = append_elevation(next_point[1][0], next_point[1][1], self.GMAPS_KEY)
                dist_m = distance_in_meters((self._posf[0], self._posf[1]), (final_point[0],final_point[1]))
                if self.SLOW_BUT_STEALTH:
                    if dist_m < 10:
                        sleep(dist_m/1.5)
                    else:
                        sleep(dist_m/2.5)
                #self.log.info("Final_point latitude: %s, longitude: %s. Distance %i meters", final_point[0],final_point[1],dist_m)
                self.api.set_position(*final_point)
                # make sure we have atleast 1 ball
                self.nearby_map_objects()

                nearby_forts = PoGObot.from_iterable_to_chain(lambda c: c.get('forts', []), self.map_cells)
                nearby_forts = [(fort, distance_in_meters(self._posf, (fort['latitude'], fort['longitude']))) for fort in nearby_forts if fort.get('type', None) == 1]
                sorted_forts = sorted(nearby_forts, lambda x, y: cmp(x[1], y[1]))
                for x in sorted_forts:
                    destinations = [x]
                    break

                if len(destinations) > 0:
                    #self.log.info('Destinations: \n\r{}'.format(json.dumps(destinations, indent=2)))
                    i = 0
                    for find_fort_near in destinations:
                        #self.log.info("Nearby fort: : %s", find_fort_near)
                        if find_fort_near[1] < 35:
                            if self.SLOW_BUT_STEALTH:
                                sleep(6 * random.random() + 3)

                            self.fort_spin(find_fort_near)
                            if find_fort_near[0]['id'] == self.walk_fort_id:
                                return
                
                if sum(self.pokeballs) > 0 and self._walk_count % 5:
                    while self.catch_near_pokemon():
                        if self.SLOW_BUT_STEALTH:
                            sleep(2 * random.random() + 2) # If you want to make it faster, delete this line... would not recommend though
        if find_fort_near[1] > 10:
            if self.SLOW_BUT_STEALTH:
                sleep(4 * random.random() + 4) # If you want to make it faster, delete this line... would not recommend though
            posf = self.api.get_position()
            #print ("posf: ", posf, find_fort_near[0]['latitude'], find_fort_near[0]['longitude'])
            #posf[0] = find_fort_near[0]['latitude']
            #posf[1] = find_fort_near[0]['longitude']
            self.api.set_position(find_fort_near[0]['latitude']+0.00001, find_fort_near[0]['longitude']-0.00001, posf[2])
            self.nearby_map_objects()
            #self._posf = self.api.get_position()

        return


    def fort_spin(self, fort_near):
        #print ("I'm in fort_spin")

        y = 0
        flag = 0
        for x in self.finished_forts:
            #print ("x= ", x)
            now = int(round(time.time()))
            if x['fort_id'] == fort_near[0]['id'] and x['spinned_time'] >= (now - 300):
                flag = 1
            
            #print (x.get('spinned_time'))
            if x['spinned_time'] < (now - 300):
                print ("delete this id from finished_forts: ", x['fort_id'])
                self.finished_forts.pop(y)
            y += 1

        if flag == 0:
            position = self._posf
            self.log.info("fort_spin fort_id: %s, fort_latitude %s, fort_longitude %s, distance %i", fort_near[0]['id'],fort_near[0]['latitude'],fort_near[0]['longitude'],fort_near[1])
            request = self.api.create_request()
            request.fort_search(fort_id=fort_near[0]['id'], fort_latitude=fort_near[0]['latitude'], fort_longitude=fort_near[0]['longitude'], player_latitude=position[0], player_longitude=position[1])
            res = request.call()['responses']['FORT_SEARCH']
            #self.log.info("fort_spin (res): %s", res)
            if 'items_awarded' in res:
                self.log.info("Fort spinned!")
                self.finished_forts = [{'fort_id': fort_near[0]['id'],'spinned_time': int(round(time.time()))}]
            # now i fully understand java's switch/case
            elif res['result'] == 3:
                self.log.info("Fort already spinned (cooling down)!")
                self.log.info("Finished_forts: %s", self.finished_forts)
            else:
                self.log.info("Fort not spinned succesfully!")
            if self.SLOW_BUT_STEALTH:
                sleep(4 * random.random() + 3)
                    
                    
    # this is in charge of spinning a pokestop
    def spin_near_fort(self):
        #response = self.nearby_map_objects()
        #sleep(2 * random.random() + 5)
        #self.response_parser(response)
        #map_cells = response.get('responses', {}).get('GET_MAP_OBJECTS', {}).get('map_cells', {})
        #self.forts = PoGObot.from_iterable_to_chain(lambda c: c.get('forts', []), map_cells)
        
        #map_cells = self.map_cells_w.get('responses', {}).get('GET_MAP_OBJECTS', {}).get('map_cells', {})
        #print ("map_cells", map_cells)
        #nearby_forts = PoGObot.from_iterable_to_chain(lambda c: c.get('forts', []), map_cells)
        	
        	
        nearby_forts = PoGObot.from_iterable_to_chain(lambda c: c.get('forts', []), self.map_cells)
        #nearby_pokemons = PoGObot.from_iterable_to_chain(lambda c: c.get('catchable_pokemons', []), self.map_cells)

        # check if there are GPX data
        if len(self.GPX_lat) == len(self.GPX_lon) and len(self.GPX_lat) > 0:
            if self._walk_count < len(self.GPX_lon):
                self.set_position(self.GPX_lat[self._walk_count], self.GPX_lon[self._walk_count], 20)
                self._walk_count += 1
                available_forts = filtered_forts((self.GPX_lat[self._walk_count], self.GPX_lon[self._walk_count]), nearby_forts)
                sleep(1 * random.random() + 1)
                for fort in available_forts:
                    if fort[1] < 10:
                        request = self.api.create_request()
                        request.fort_search(fort_id=fort['id'], fort_latitude=fort['latitude'], fort_longitude=fort['longitude'], player_latitude=self.GPX_lat[self._walk_count], player_longitude=self.GPX_lon[self._walk_count])
                        res = request.call()['responses']['FORT_SEARCH']
                        if 'lure_info' in fort:
                            encounter_id = fort['lure_info']['encounter_id']
                            fort_id = fort['lure_info']['fort_id']
                            resp = self.api.disk_encounter(encounter_id=encounter_id, fort_id=fort_id, player_latitude=self.GPX_lat[self._walk_count], player_longitude=self.GPX_lon[self._walk_count]).call()['responses']['DISK_ENCOUNTER']
                            if self.pokeballs[1] > 9 and self.pokeballs[2] > 4 and self.pokeballs[3] > 4:
                                self.disk_encounter_pokemon(fort['lure_info'])
            else:
                self.walk_count = 0
                #self.spin_near_fort
        # without GPX data bot wil go from pokestop to pokestop
        else:
            #print ("Str 270")
            #print (self._start_pos)
            #print (self._walk_count)
            #print (self.config.get("RETURN_START_INTERVAL"))
            #print (self._walk_count % self.config.get("RETURN_START_INTERVAL"))
            
            
            #near_fort = [{'last_modified_timestamp_ms': 1471348086825L, 'enabled': True, 'longitude': 30.346832, 'latitude': 50.281982, 'type': 1, 'id': u'9fcf7d596c1c46b0b86cded933b6f132.16'}, {'last_modified_timestamp_ms': 1467338156329L, 'enabled': True, 'longitude': 30.34095, 'latitude': 50.271207, 'type': 1, 'id': u'62175c81de5d403b8f6b21c67fc3a0d3.16'}]
            #print ("nearby_forts: ", nearby_forts)

            #nearby_forts = [(fort, round(vincenty(self._start_pos, (fort['latitude'], fort['longitude'])).meters)) for fort in nearby_forts if fort.get('type', None) == 1]
            #nearby_forts = [(fort, distance_in_meters(self._start_pos, (fort['latitude'], fort['longitude']))) for fort in nearby_forts if fort.get('type', None) == 1]
            #print ("nearby_forts: ", nearby_forts)
            #print("sorted_forts: ", sorted_forts)
            
            if self._start_pos and self._walk_count % self.config.get("RETURN_START_INTERVAL") == 0:
                nearby_forts = [(fort, distance_in_meters(self._start_pos, (fort['latitude'], fort['longitude']))) for fort in nearby_forts if fort.get('type', None) == 1]
                #destinations = filtered_forts(self._start_pos, nearby_forts)
            else:
                nearby_forts = [(fort, distance_in_meters(self._posf, (fort['latitude'], fort['longitude']))) for fort in nearby_forts if fort.get('type', None) == 1]
                #destinations = filtered_forts(self._posf, nearby_forts)
            sorted_forts = sorted(nearby_forts, lambda x, y: cmp(x[1], y[1]))
            destinations = [x for x in sorted_forts]

            #print ("count forts :", len(sorted_forts))
            #print ("destinations: ", destinations, len(destinations))
            
            if len(destinations) > 0:
                # select a random pokestop and go there
                destination_num = random.randint(2, min(7, len(destinations) - 1))
                #destination_num = 0 #go to the nearest pokestop
                #for find_fort_near in destinations:
                    #print (find_fort_near)
                    #if "cooldown_complete_timestamp_ms" not in find_fort_near:
                        #fort = find_fort_near
                        #break
                fort = destinations[destination_num]
                #print ("fort", fort)
                if self._walk_count == 1:
                    self.first_fort = fort
                if self._start_pos and self._walk_count % self.config.get("RETURN_START_INTERVAL") == 0:
                    fort = self.first_fort
                
                self.log.info("Walking to fort at %s,%s", fort[0]['latitude'], fort[0]['longitude'])
                self.walk_fort_id = fort[0]['id']
                self.walk_to((fort[0]['latitude'], fort[0]['longitude']))
                self.log.info("Arrived at fort at %s,%s", fort[0]['latitude'], fort[0]['longitude'])
                if self.SLOW_BUT_STEALTH:
                    sleep(6 * random.random() + 3)
                # when arrived, get the new position and spin the pokestop
                #self._posf = self.api.get_position()
                
                #self.fort_spin(fort)

                #position = self._posf
                #request = self.api.create_request()
                #request.fort_search(fort_id=fort[0]['id'], fort_latitude=fort[0]['latitude'], fort_longitude=fort[0]['longitude'], player_latitude=position[0], player_longitude=position[1])
                #res = request.call()['responses']['FORT_SEARCH']
                #if 'items_awarded' in res:
                    #self.log.info("Fort spinned!")
                # now i fully understand java's switch/case
                #elif res['result'] == 3:
                    #self.log.info("Fort already spinned (cooling down)!")
                #else:
                    #self.log.info("Fort not spinned succesfully!")

                #if 'lure_info' in fort:
                    #encounter_id = fort['lure_info']['encounter_id']
                    #fort_id = fort['lure_info']['fort_id']
                    #request_2 = self.api.create_request()
                    #request_2.disk_encounter(encounter_id=encounter_id, fort_id=fort_id, player_latitude=position[0], player_longitude=position[1])
                    #resp = request_2.call()['responses']['DISK_ENCOUNTER']
                    #self.log.debug('Encounter response is: %s', resp)
                    #if sum(self.pokeballs) > 10:
                        #self.disk_encounter_pokemon(fort['lure_info'])
                return True
            else:
                self.log.error("No fort to walk to!")
                return False

    # this will catch any nearby pokemon
    def catch_near_pokemon(self):
        #map_cells = self.nearby_map_objects().get('responses', {}).get('GET_MAP_OBJECTS', {}).get('map_cells', {})
        #pokemons = PoGObot.from_iterable_to_chain(lambda c: c.get('catchable_pokemons', []), map_cells)
        #self.nearby_pokemons
        #sleep(3 * random.random() + 5)
        # cache map cells for api
        #self.map_cells = map_cells
        # catch first pokemon:
        #print (len(pokemons))
        #print (pokemons)
        #for fort1 in pokemons:
            #print ("pokemon1",fort1)
        nearby_pokemons = PoGObot.from_iterable_to_chain(lambda c: c.get('catchable_pokemons', []), self.map_cells)
        origin = (self._posf[0], self._posf[1])
        pokemon_distances = [(pokemon, distance_in_meters(origin, (pokemon['latitude'], pokemon['longitude']))) for pokemon in nearby_pokemons]
        if len(pokemon_distances) > 0:
            self.log.debug("Nearby pokemon: : %s", pokemon_distances)
            for pokemon_distance in pokemon_distances:
                target = pokemon_distance
                #print (target)
                self.log.debug("Catching pokemon: : %s, distance: %f meters", target[0], target[1])
                self.log.info("Catching Pokemon: %s, latitude: %s, longitude: %s, distance: %i meters", self.pokemon_names[str(target[0]['pokemon_id'])], target[0]['latitude'],target[0]['longitude'],target[1])
                #return self.encounter_pokemon(target[0])
                self.encounter_pokemon(target[0])
        return False

    def nearby_map_objects(self):
        self._posf = self.api.get_position()
        if (self.last_map_request['latitude'] != self._posf[0] and self.last_map_request['longitude'] != self._posf[1]) or (int(round(time.time())) - self.last_map_request['time']) > 10:
            cell_ids = util.get_cell_ids(lat=self._posf[0], long=self._posf[1], radius=700)
            timestamps = [0, ] * len(cell_ids)
            #self.log.info("Nearby_map_objects latitude: %s, longitude: %s", self._posf[0],self._posf[1])
            self.map_cells_w = self.api.get_map_objects(latitude=self._posf[0], longitude=self._posf[1], since_timestamp_ms=timestamps, cell_id=cell_ids)
            self.response_parser(self.map_cells_w)
            
            self.last_map_request['time'] = int(round(time.time()))
            self.last_map_request['latitude'] = self._posf[0]
            self.last_map_request['longitude'] = self._posf[1]
            #self.log.info('nearby_map_objects (self.map_cells_w): \n\r{}'.format(json.dumps(self.map_cells_w, indent=2)))
            
            self.map_cells = self.map_cells_w.get('responses', {}).get('GET_MAP_OBJECTS', {}).get('map_cells', {})
 
        return True

    def attempt_catch(self, encounter_id, spawn_point_id, ball_type):
        r = self.api.catch_pokemon(
            normalized_reticle_size=1.950,
            pokeball=ball_type,
            spin_modifier=0.850,
            hit_pokemon=True,
            normalized_hit_position=1,
            encounter_id=encounter_id,
            spawn_point_id=spawn_point_id,
        )['responses']['CATCH_POKEMON']
        self.log.info("Throwing pokeball type: %s", POKEBALLS[ball_type - 1]) # list the pokeball that was thrown
        if "status" in r:
            self.log.debug("Status: %d", r['status'])
            return r

    def cleanup_inventory(self, inventory_items=None):
        if not inventory_items:
            inventory_items = self.api.get_inventory().call()['responses']['GET_INVENTORY']['inventory_delta']['inventory_items']
        sleep(3 * random.random() + 5)
        all_actual_items = [xiq['inventory_item_data']["item"] for xiq in inventory_items if "item" in xiq['inventory_item_data']]
        all_actual_item_str = "\n\nList of items:\n\n"
        all_actual_item_count = 0
        all_actual_items = sorted([x for x in all_actual_items if "count" in x], key=lambda x: x["item_id"])
        for xiq in all_actual_items:
            if 1 <= xiq["item_id"] <= 4: # save counts of pokeballs
                self.pokeballs[xiq["item_id"]] = xiq["count"]
            true_item_name = INVENTORY_DICT[xiq["item_id"]]
            all_actual_item_str += "Item_ID " + str(xiq["item_id"]) + "\titem count " + str(xiq["count"]) + "\t(" + true_item_name + ")\n"
            all_actual_item_count += xiq["count"]
        all_actual_item_str += "\nTotal item count: " + str(all_actual_item_count) + "\n"
        self.log.info(all_actual_item_str)

        caught_pokemon = defaultdict(list)
        for inventory_item in inventory_items:
            if "pokemon_data" in inventory_item['inventory_item_data']:
                # This code block checks to see if the inventory item is an item or pokemon
                pokemon = inventory_item['inventory_item_data']['pokemon_data']
                if 'cp' in pokemon and "favorite" not in pokemon:
                    caught_pokemon[pokemon['pokemon_id']].append(pokemon)
            elif "item" in inventory_item['inventory_item_data']:
                item = inventory_item['inventory_item_data']['item']  # Check to see if your holding too many items and recycles them
                if item['item_id'] in self.min_item_counts and "count" in item and item['count'] > self.min_item_counts[item['item_id']]:
                    recycle_count = item['count'] - self.min_item_counts[item['item_id']]
                    self.log.debug("Recycling {0}, item count {1}".format(INVENTORY_DICT[item['item_id']], recycle_count))
                    self.api.recycle_inventory_item(item_id=item['item_id'], count=recycle_count)

        for pokemons in caught_pokemon.values():
            if len(pokemons) > MIN_SIMILAR_POKEMON:  # if you have more than 1 of the same amount of pokemon do this
                pokemons = sorted(pokemons, lambda x, y: cmp(x['cp'], y['cp']), reverse=True)
                for pokemon in pokemons:
                    if pokemon['pokemon_id'] in CANDY_NEEDED_TO_EVOLVE:
                        for inventory_item in inventory_items:
                            if "pokemon_family" in inventory_item['inventory_item_data'] and (inventory_item['inventory_item_data']['pokemon_family']['family_id'] == pokemon['pokemon_id'] or inventory_item['inventory_item_data']['pokemon_family']['family_id'] == (pokemon['pokemon_id'] - 1)) and inventory_item['inventory_item_data']['pokemon_family'].get('candy', 0) > CANDY_NEEDED_TO_EVOLVE[pokemon['pokemon_id']] and pokemon['pokemon_id'] not in self.evolved_pokemon_ids:
                                self.log.info("Evolving pokemon: %s", self.pokemon_names[str(pokemon['pokemon_id'])])
                                #self.api.evolve_pokemon(pokemon_id=pokemon['id'])  # quick press ctrl + c to stop the evolution
                                self.evolved_pokemon_ids.append(pokemon['pokemon_id'])
                                if self.SLOW_BUT_STEALTH:
                                    sleep(3 * random.random() + 28)
        excess_pokemons = defaultdict(list)
        #print ("Str 407: ", excess_pokemons)
        for pokemons in caught_pokemon.values():
            pokemons = sorted(pokemons, key=lambda x: x['pokemon_id'])

            poke_list_one = []
            poke_list_new = []
            
            pok_id = 0
            for pokemon in pokemons:
              if pok_id == pokemon['pokemon_id']:
                poke_list_one.append(pokemon)
              else:
                if len(poke_list_one) > 0:
                  poke_list_one = sorted(poke_list_one, key=lambda x: x['cp'], reverse=True)
                  for poke_list_one1 in poke_list_one:
                    poke_list_new.append(poke_list_one1)
                poke_list_one = []
    
                poke_list_one.append(pokemon)
                pok_id = pokemon['pokemon_id']

            if len(poke_list_one) > 0:
              poke_list_one = sorted(poke_list_one, key=lambda x: x['cp'], reverse=True)
              for poke_list_one1 in poke_list_one:
                poke_list_new.append(poke_list_one1)
              poke_list_one = []
  
            pokemons = poke_list_new
            poke_list_one = []
            poke_list_new = []
            pok_id = 0
            
            if self.RELEASE_DUPLICATES:
                for pokemon in pokemons:
                    #print ("pokemon: ", pokemon['pokemon_id'], pokemon['cp'], pokemon['individual_defense'], pokemon['individual_attack'], pokemon_iv_percentage(pokemon)) 
                    #print ("pokemon: ", pokemon)
                    #print (" ")

                    if pok_id == 0:
                        top_CP_pokemon = pokemon
                        pok_id = pokemon['pokemon_id']
                    elif pok_id == pokemon['pokemon_id'] and pokemon['cp'] < self.KEEP_CP_OVER and pokemon_iv_percentage(pokemon) < self.MIN_KEEP_IV and top_CP_pokemon['cp'] * self.DUPLICATE_CP_FORGIVENESS > pokemon['cp'] and "favorite" not in pokemon:
                    	
                        excess_pokemons[pokemon['pokemon_id']].append(pokemon)
                        self.log.debug('Excess pokemon: %s CP: %s IV: %s', self.pokemon_names[str(pokemon['pokemon_id'])], pokemon['cp'], pokemon_iv_percentage(pokemon))
                    elif pok_id != pokemon['pokemon_id']:
                        top_CP_pokemon = pokemon
                        pok_id = pokemon['pokemon_id']                        
                
                #print ("Str 451: ", excess_pokemons)
                for pokemons_id in excess_pokemons.keys():
                    #print ("Str 412: ", pokemons_id)
                    pokemons = excess_pokemons.pop(pokemons_id)
                    #print (pokemons)
                    for pokemon in pokemons:
                        atgym = 'deployed_fort_id' in pokemon
                        if atgym:
                            self.log.info("Pokemon %s CP: %s not released because at gym", self.pokemon_names[str(top_CP_pokemon['pokemon_id'])], top_CP_pokemon['cp'])
                        if not atgym:
                            self.log.debug("Releasing pokemon: %s", pokemon)
                            self.log.info("Releasing pokemon: %s CP: %s IV: %s", self.pokemon_names[str(pokemon['pokemon_id'])], pokemon['cp'], pokemon_iv_percentage(pokemon))
                            self.api.release_pokemon(pokemon_id=pokemon["id"])
                            sleep(3 * random.random() + 5)
        return

    def disk_encounter_pokemon(self, lureinfo):
        try:
            encounter_id = lureinfo['encounter_id']
            fort_id = lureinfo['fort_id']
            position = self._posf
            resp = self.api.disk_encounter(encounter_id=encounter_id, fort_id=fort_id, player_latitude=position[0], player_longitude=position[1]).call()['responses']['DISK_ENCOUNTER']
            sleep(2 * random.random() + 1)
            if resp['result'] == 1:
                capture_status = -1
                self._pokeball_type = 1
                while capture_status != 0 and capture_status != 3:
                    for balls in range(len(self.pokeballs)):
                        self._pokeball_type = balls
                        if self.pokeballs[balls] > 0:
                            catch_attempt = self.attempt_catch(encounter_id, fort_id, self._pokeball_type)
                            self.pokeballs[self._pokeball_type] -= 1
                            capture_status = catch_attempt['status']
                            if capture_status == 1:
                                self.log.debug("Caught Pokemon: : %s", catch_attempt)
                                self.log.info("Caught Pokemon:  %s", self.pokemon_names[str(resp['pokemon_data']['pokemon_id'])])
                                self._pokeball_type = 1
                                if self.SLOW_BUT_STEALTH:
                                    sleep(2 * random.random() + 2)
                                else:
                                    sleep(2)
                                return catch_attempt
                            elif capture_status == 2:
                                self.log.info("Pokemon %s is too wild", self.pokemon_names[str(resp['pokemon_data']['pokemon_id'])])
                                if self._pokeball_type < self.MAX_BALL_TYPE:
                                    self._pokeball_type += 1
                                if self.SLOW_BUT_STEALTH:
                                    sleep(3 * random.random() + 2)
                            elif capture_status == 3:
                                self.log.debug("Failed Catch: : %s", catch_attempt)
                                self.log.info("Failed to Catch Pokemon:  %s", self.pokemon_names[str(resp['pokemon_data']['pokemon_id'])])
                                self._pokeball_type = 1
                    if self.SLOW_BUT_STEALTH:
                        sleep(3 * random.random() + 2)
                    else:
                        sleep(1)
            return False
        except Exception as e:
            self.log.error("Error in disk encounter %s", e)
            self._pokeball_type = 1
            return False

    def encounter_pokemon(self, pokemon):
        encounter_id = pokemon['encounter_id']
        spawn_point_id = pokemon['spawn_point_id']
        position = self._posf
        # contact the servers
        request = self.api.create_request()
        request.encounter(
            encounter_id=encounter_id,
            spawn_point_id=spawn_point_id,
            player_latitude=position[0],
            player_longitude=position[1]
        )
        response = request.call()
        encounter = response['responses']['ENCOUNTER']
        # this cade catches pokemon
        self.log.debug("Started Encounter: %s", encounter)
        #self.log.info("Started Encounter: %s", encounter)
        if encounter['status'] == 1:
            capture_status = -1
            self._pokeball_type = 1  # start with a pokeball
            while capture_status != 0 and capture_status != 3:
                for balls in range(len(self.pokeballs)):  # try with each ball type starting with weakest
                    self._pokeball_type = balls
                    if self.pokeballs[balls] > 0:  # if you have less then 1 ball do not attempt to catch em all
                        catch_attempt = self.attempt_catch(encounter_id, spawn_point_id, self._pokeball_type)  # actual catching code
                        self.pokeballs[self._pokeball_type] -= 1  # lowers the thrown ball code
                        capture_status = catch_attempt['status']
                        if capture_status == 1:
                            self.log.debug("Caught Pokemon: : %s", catch_attempt)  # you did it
                            self.log.info("Caught Pokemon:  %s", self.pokemon_names[str(pokemon['pokemon_id'])])
                            self._pokeball_type = 1
                            if self.SLOW_BUT_STEALTH:
                                sleep(3 * random.random() + 3)
                            else:
                                sleep(2)
                            return catch_attempt
                        elif capture_status == 2:
                            self.log.info("Pokemon %s is too wild", self.pokemon_names[str(pokemon['pokemon_id'])])
                            if self._pokeball_type < self.MAX_BALL_TYPE:
                                self._pokeball_type += 1  # try with a stronger ball
                            if self.SLOW_BUT_STEALTH:
                                sleep(3 * random.random() + 2)
                        elif capture_status == 3:
                            self.log.debug("Failed Catch: : %s", catch_attempt)  # potential soft ban or just a run away
                            self.log.info("Failed to Catch Pokemon:  %s", self.pokemon_names[str(pokemon['pokemon_id'])])
                            self._pokeball_type = 1
                if self.SLOW_BUT_STEALTH:
                    sleep(3 * random.random() + 2)
                else:
                    sleep(2)
        return False

    def login(self, provider, username, password, cached=False):

        # set player position on the earth
        self.api.set_position(*self._start_pos)

        # new authentication initialitation
        self.api.set_authentication(provider=provider, username=username, password=password)

        # provide the path for your encrypt dll
        encryption_path = self.get_encryption_lib_path()
        self.api.activate_signature(encryption_path)

        # try to log in like real app
        response = self.api.app_simulation_login()

        # update Inventory
        self.response_parser(res=response)

        sleep(5 * random.random() + 5)

        return True

    def get_encryption_lib_path(self):
        lib_path = ""
        # win32 doesn't mean necessarily 32 bits
        if sys.platform == "win32":
            if platform.architecture()[0] == '64bit':
                lib_path = os.path.join(os.path.dirname(__file__), "../pgoapi/libs/libencrypt-windows-64.dll")
            else:
                lib_path = os.path.join(os.path.dirname(__file__), "../pgoapi/libs/libencrypt-windows-32.dll")

        elif sys.platform == "darwin":
            lib_path = os.path.join(os.path.dirname(__file__), "../pgoapi/libs/libencrypt-osx-64.so")

        elif os.uname()[4].startswith("arm") and platform.architecture()[0] == '32bit':
            lib_path = os.path.join(os.path.dirname(__file__), "../pgoapi/libs/libencrypt-linux-arm-32.so")

        elif sys.platform.startswith('linux'):
            if platform.architecture()[0] == '64bit':
                lib_path = os.path.join(os.path.dirname(__file__), "../pgoapi/libs/libencrypt-linux-x86-64.so")
            else:
                lib_path = os.path.join(os.path.dirname(__file__), "../pgoapi/libs/libencrypt-linux-x86-32.so")

        else:
            err = "Unexpected/unsupported platform '{}'".format(sys.platform)
            self.log.info(err)
            raise Exception(err)

        if not os.path.isfile(lib_path):
            err = "Could not find {} encryption library {}".format(sys.platform, lib_path)
            self.log.info(err)
            raise Exception(err)

        return lib_path

    def set_GPX(self):
        #print ("I'm in set_GPX")
        #print (len(self.GPX_lat), len(self.GPX_lon))
        if len(self.GPX_lat) == 0 and len(self.GPX_lon) == 0:
            try:
                tree = ETXML.parse('GPX.xml')
                root = tree.getroot()
                trk = root.getiterator()
                point_number = len(trk) - 1
                self.log.info('\n\n' + str(point_number) + ' points found' + '\nTrak location: ' + trk[2].text + '\n')
                for i in range(5, point_number):
                    if str(trk[i].get('lat')) != str(None):
                        self.GPX_lat.append(float(trk[i].get('lat')))
                        self.GPX_lon.append(float(trk[i].get('lon')))
                        return True
            except:
                self.log.debug('GPX data not found or some error has occured')
                return False

    def attempt_hatch_eggs(self, res=None):
        if not res:
            res = self.api.get_inventory().call()
        hatching_incubator_list, empty_incubator_list = get_incubators_stat(res)
        hatching_eggs, immature_eggs = get_eggs_stat(res)
        hatching_eggs_count = 0
        for immature_egg in immature_eggs:
            egg_id = immature_egg['pokemon_data']['id']
            if len(empty_incubator_list) > 0:
                # Always use first incubator.
                incubator_index = 0
                incubator_id = empty_incubator_list[incubator_index]['id']
                uses_remaining = empty_incubator_list[incubator_index].get('uses_remaining', 0) - 1
                if self.hatch_egg(incubator_id, egg_id):
                    hatching_eggs_count += 1
                    # Update incubator manually to save api call().
                    empty_incubator_list[incubator_index]['uses_remaining'] = uses_remaining
                    if uses_remaining <= 0:
                        del(empty_incubator_list[incubator_index])
        return hatching_eggs_count

    def hatch_egg(self, incubator_id, egg_id):
        # contact the servers
        request = self.api.create_request()
        request.use_item_egg_incubator(item_id=incubator_id, pokemon_id=egg_id)
        response = request.call()
        sleep(random.random() + 1)
        result = response.get('responses', {}).get('USE_ITEM_EGG_INCUBATOR', {})
        if len(result) == 0:
            return False
        if "result" in result:
            self.log.debug("Result: %d", result['result'])
        return result.get('result', 0) == 1

    def main_loop(self):
        self.set_GPX()
        heartbeat_cnt = 3

        self.nearby_map_objects()
        nearby_forts = PoGObot.from_iterable_to_chain(lambda c: c.get('forts', []), self.map_cells)
        #nearby_pokemons = PoGObot.from_iterable_to_chain(lambda c: c.get('catchable_pokemons', []), self.map_cells_w)

        #print (nearby_forts)
        #for near_fort in nearby_forts:
            #self.log.info('main_loop (nearby_fort): \n\r{}'.format(json.dumps(near_fort, indent=2)))
       
        while True:
            if heartbeat_cnt % 3 == 0:
                try:
                    self.heartbeat()
                    sleep(1 * random.random() + 2) # If you want to make it faster, delete this line... would not recommend though
                except ServerSideRequestThrottlingException:
                    self.log.info("Too frequent requests, slow down man! (self.heartbeat)")
                    for i in range(5, 1, -1):
                        self.log.info("Wait %s more seconds befrore continuing", str(i))
                        sleep(100)
            
            heartbeat_cnt += 1
            #try:
                #if sum(self.pokeballs) > 0:  # if you do not have any balls skip pokemon catching
                    #while self.catch_near_pokemon():
                        #sleep(1 * random.random() + 2) # If you want to make it faster, delete this line... would not recommend though
                #else:
                    #self.log.info("Less than 1 Poke Balls: Entering pokestops only")
            #except ServerSideRequestThrottlingException:
                #self.log.info("Too frequent requests, slow down man! (self.catch_near_pokemon)")
                #for i in range(5, 1, -1):
                    #self.log.info("Wait %s more seconds befrore continuing", str(i))
                    #sleep(100)

            try:
                self.spin_near_fort()  # check local pokestop
            except ServerSideRequestThrottlingException:
                self.log.info("Too frequent requests, slow down man! (self.spin_near_fort)")
                for i in range(5, 1, -1):
                    self.log.info("Wait %s more seconds befrore continuing", str(i))
                    sleep(100)
                #self.main_loop()
            if self.SLOW_BUT_STEALTH:
                sleep(3 * random.random() + 2)


    @staticmethod
    def from_iterable_to_chain(f, items):
        return chain.from_iterable(imap(f, items))
