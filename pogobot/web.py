from __future__ import absolute_import

import flask
import logging
import json
import os

from flask.helpers import send_from_directory
from flask import Flask

log = logging.getLogger(__name__)

app = Flask(__name__)


class PoGoServer:
    def __init__(self):
        pass

app = Flask(__name__)
pogo_server = PoGoServer()


@app.before_first_request
def setup_logging():
    if not app.debug:
        # In production mode, add log handler to sys.stderr.
        app.logger.addHandler(logging.StreamHandler())
        app.logger.setLevel(logging.ERROR)


@app.route('/')
def index():
    return send_from_directory('views', 'index.html')


@app.route('/resources/<path:path>')
def send_js(path):
    return send_from_directory('resources', path)


@app.route('/api/player')
def api_player():
    if os.path.isfile("accounts/%s/Player.json" % pogo_server.bot.config['username']):
        with open("accounts/%s/Player.json" % pogo_server.bot.config['username'], "r") as file_to_read:
            file = file_to_read.read()
            res = json.loads(file)
            data = res['GET_PLAYER']['player_data']
    else:
        data = ["No data found"]
    return flask.jsonify(data)


@app.route('/api/player/profile')
def api_player_profile():
    res = pogo_server.bot.api.get_player_profile().call()
    data = res['responses']['GET_PLAYER_PROFILE']
    return flask.jsonify(data)


@app.route('/api/inventory')
def api_inventory():
    if os.path.isfile("accounts/%s/Inventory.json" % pogo_server.bot.config['username']):
        with open("accounts/%s/Inventory.json" % pogo_server.bot.config['username'], "r") as file_to_read:
            file = file_to_read.read()
            res = json.loads(file)
            data = res['GET_INVENTORY']['inventory_delta']['inventory_items']
    else:
        data = ["No data found"]
    return flask.jsonify(data)


@app.route('/api/location')
def api_location():
    lla = pogo_server.bot.api.get_position()
    data = dict()
    data['lat'] = lla[0]
    data['lng'] = lla[1]
    data['alt'] = lla[2]
    return flask.jsonify(data)


@app.route('/api/nearby')
def api_nearby():
    data = pogo_server.bot.map_cells or dict()
    return flask.jsonify(data)


@app.route('/api/pokemon_names')
def api_pokemon_names():
    print(pogo_server.bot)
    return flask.jsonify(pogo_server.bot.pokemon_names)


def start_server(bot, port):
    logging.getLogger("_internal").setLevel(logging.ERROR)  # Silence flask
    pogo_server.bot = bot
    app.run(host="0.0.0.0", port=port, debug=False, use_reloader=False, threaded=True)
