# Just a random python bot

# Do NOT use this bot while signed into your phone

# If you want to make the bot as fast as possible for catching more pokemon (like you are driving a fast car--it won't look suspicious though, since it only goes on paths), make stepsize 200; for more info see that method in pgoapi.py under pgoapi...but still I wouldn't recommend making stepsize that high

import os
# import re
import json
# import struct
import logging
# import requests
import argparse
import thread
from time import sleep

# add directory of this file to PATH, so that the package will be found
# import sys
# sys.path.append(os.path.dirname(os.path.realpath(__file__)))

# from pgoapi import PGoApi
from pogobot import pogobot, web
# from utilities import f2i, h2f
# from location import get_neighbors

# from google.protobuf.internal import encoder
from geopy.geocoders import GoogleV3
# from s2sphere import CellId, LatLng

log = logging.getLogger(__name__)


def get_pos_by_name(location_name):
    geolocator = GoogleV3()
    #print (location_name)
    loc = geolocator.geocode(location_name)
    log.info('Your given location: %s', loc.address.encode('utf-8'))
    log.info('lat/long/alt: %s %s %s', loc.latitude, loc.longitude, loc.altitude)
    return (loc.latitude, loc.longitude, loc.altitude)
    # If you are having problems with the above three lines; that means your API isn't configured or it expired or something happened related to api. If that is the case, just manually input the coordinates of you current location. Don't make it something too ridiculous, or it might result in a soft ban. For example, you would replace the above three lines with something like: return (33.0, 112.0, 0.0)


def init_config():
    parser = argparse.ArgumentParser()
    config_file = "config.json"
    load = {}
    if os.path.isfile(config_file):
        with open(config_file) as data:
            load.update(json.load(data))

    def required(x):
        return x not in load['accounts'][0].keys()

    parser.add_argument("-a", "--auth_service", help="Auth Service ('ptc' or 'google')",
                        required=required("auth_service"))
    parser.add_argument("-i", "--config_index", help="config_index", required=required("config_index"))
    parser.add_argument("-u", "--username", help="Username", required=required("username"))
    parser.add_argument("-p", "--password", help="Password", required=required("password"))
    parser.add_argument("-l", "--location", help="Location", required=required("location"))
    parser.add_argument("-v", "--verbose", help="Debug Mode", action='store_true')
    parser.add_argument("-c", "--cached", help="cached", action='store_true')
    parser.add_argument("-t", "--test", help="Only parse the specified location", action='store_true')
    parser.set_defaults(DEBUG=False, TEST=False, CACHED=False)
    config = parser.parse_args()
    load = load['accounts'][int(config.__dict__['config_index'])]
    config.__dict__.update(load)
    if config.auth_service not in ['ptc', 'google']:
        log.error("Invalid Auth service specified! ('ptc' or 'google')")
        return None

    return config


def main():
    logging.basicConfig(level=logging.WARNING, format='%(asctime)s [%(module)10s] [%(levelname)5s] %(message)s')
    logging.getLogger("requests").setLevel(logging.WARNING)
    logging.getLogger("pogobot").setLevel(logging.INFO)
    logging.getLogger("pgoapi").setLevel(logging.INFO)
    logging.getLogger("rpc_api").setLevel(logging.INFO)

    config = init_config()
    if not config:
        return

    if config.verbose:
        logging.getLogger("requests").setLevel(logging.DEBUG)
        logging.getLogger("pogobot").setLevel(logging.DEBUG)
        logging.getLogger("pgoapi").setLevel(logging.DEBUG)
        logging.getLogger("rpc_api").setLevel(logging.DEBUG)

    position = get_pos_by_name(config.location)
    #print (config.location)
    #print (position)
    if config.test:
        return

    pokemon_names = json.load(open("name_id.json"))

    # there we creates the dump files is not already present
    if not os.path.exists("accounts/%s/" % config.username):
        os.mkdir("accounts/%s/" % config.username)
    if not os.path.isfile("accounts/%s/Inventory.json" % config.username):
        with open("accounts/%s/Inventory.json" % config.username, "w") as f:
                f.write(json.dumps({}, indent=2))
                f.close()
    if not os.path.isfile("accounts/%s/Map.json" % config.username):
        with open("accounts/%s/Map.json" % config.username, "w") as f:
                f.write(json.dumps({}, indent=2))
                f.close()
    if not os.path.isfile("accounts/%s/Player.json" % config.username):
        with open("accounts/%s/Player.json" % config.username, "w") as f:
                f.write(json.dumps({}, indent=2))
                f.close()

    # initialize the bot object
    bot = pogobot.PoGObot(config.__dict__, pokemon_names, position)

    thread.start_new_thread(web.start_server, (bot, config.WEB_PORT))

    # login attempt, the starts the main boot loop
    if not bot.login(config.auth_service, config.username, config.password, config.cached):
        return
    while True:
        try:
            bot.main_loop()
        except Exception as e:
            log.exception('Main loop has an ERROR, restarting %s', e)
            sleep(30)
            #main()
            break

    #import ipdb # noqa
    #ipdb.set_trace() # noqa

if __name__ == '__main__':
    main()
