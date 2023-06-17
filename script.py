from etherscan import Etherscan
import requests
import networkx
import matplotlib.pyplot as plt
import json
import numpy
import re
from datetime import datetime, timedelta
from random import randint
from scipy import stats
from variables import API_KEY
from variables import ADDRESS

api = Etherscan(API_KEY)

def get_contract_creator(addresses, api_key):
    request_args = {'module': 'contract', 'action': 'getcontractcreation', 'contractaddresses': addresses, 'apikey': api_key}
    request_result = requests.get('https://api.etherscan.io/api', params=request_args)
    return json.loads(request_result.text)['result']

def get_txs_list(address, start=0, end=99999999):
    return api.get_normal_txs_by_address(address=address, startblock=start, endblock=end, sort='asc')

def get_incoming_txs(address):
    txs_list = get_txs_list(address)
    return [transaction for transaction in txs_list if transaction['to'] == address]

def get_outcoming_txs(address):
    txs_list = get_txs_list(address)
    return [transaction for transaction in txs_list if transaction['from'] == address]

def find_creation_data(address):
    return datetime.fromtimestamp(int(get_txs_list(address)[0]['timeStamp'])).isoformat()

def count_txs_per_block(address):
    txs_list = get_txs_list(address)
    distribution = {}
    for transaction in txs_list:
        if transaction['blockNumber'] not in distribution.keys():
            distribution[transaction['blockNumber']] = 1
        distribution[transaction['blockNumber']] += 1
    return distribution

NORM_SAMPLE_SIZE = 30

def confidence_interval(address):
    distribution_values = list(count_txs_per_block(address).values())
    low_bounds = []
    top_bounds = []
    while(len(distribution_values) >= NORM_SAMPLE_SIZE):
        sample = [distribution_values.pop(randint(0, len(distribution_values) - 1)) for i in range(NORM_SAMPLE_SIZE)]
        low, top  = stats.norm.interval(alpha=0.99, loc=numpy.mean(sample), scale=stats.sem(sample))
        low_bounds.append(low)
        top_bounds.append(top)
    mean_low = numpy.mean(low_bounds)
    mean_top = numpy.mean(top_bounds)
    return mean_low, mean_top

SUSPICIOUS_DIVIATION_THRESHOLD = 2

def get_suspicious_blocks(address):
    sus_value = confidence_interval(address)[1]
    distribution = count_txs_per_block(address)
    sus = [block for block, txs in distribution.items() if txs > round(sus_value) * SUSPICIOUS_DIVIATION_THRESHOLD]
    return sus

def get_suspicious_txs(address):
    suspicious_blocks = get_suspicious_blocks(address)
    txs_list = []
    for block in suspicious_blocks:
        txs_list.extend(get_txs_list(address, int(block), int(block)))
    return txs_list

def one_layer_building(start_address, collapse_graph):
    print(start_address)
    if get_contract_creator(start_address, API_KEY) is None and len(get_txs_list(start_address)) < 25:
        outcoming_txs = get_outcoming_txs(start_address)
        for i, transaction in enumerate(outcoming_txs):
            print(i, 'of' , len(outcoming_txs))
            destination = transaction['to'] if transaction['to'] != '' else transaction['contractAddress']
            if not collapse_graph.has_edge(start_address, destination):
                if destination not in collapse_graph:
                    collapse_graph.add_node(destination, first_tx=find_creation_data(destination), points=0 if get_contract_creator(destination, API_KEY) is None else -1)
                collapse_graph.add_edge(start_address, destination, value=int(transaction['value'])/10**18, hash=[transaction['hash']])
            elif transaction['hash'] not in collapse_graph.edges[start_address, destination]['hash']:
                collapse_graph.edges[start_address, destination]['value'] += int(transaction['value'])/10**18
                collapse_graph.edges[start_address, destination]['hash'].append(transaction['hash'])

        incoming_txs = get_incoming_txs(start_address)
        for i, transaction in enumerate(incoming_txs):
            print(i, 'of' , len(incoming_txs))
            departure = transaction['from'] if transaction['from'] != '' else transaction['contractAddress']
            if not collapse_graph.has_edge(departure, start_address):
                if departure not in collapse_graph:
                    collapse_graph.add_node(departure, first_tx=find_creation_data(departure), points=0 if get_contract_creator(departure, API_KEY) is None else -1)
                collapse_graph.add_edge(departure, start_address, value=int(transaction['value'])/10**18, hash=[transaction['hash']])
            elif transaction['hash'] not in collapse_graph.edges[departure, start_address]['hash']:
                collapse_graph.edges[departure, start_address]['value'] += int(transaction['value'])/10**18
                collapse_graph.edges[departure, start_address]['hash'].append(transaction['hash'])

def build_collapse_graph(contract_address):
    collapse_graph = networkx.DiGraph()
    collapse_graph.add_node(contract_address, first_tx=find_creation_data(contract_address), points=-1)
    suspicious_txs = get_suspicious_txs(contract_address)
    for i, transaction in enumerate(suspicious_txs):
        print('pre-build' , i, 'of' , len(suspicious_txs))
        departure = transaction['from']
        if departure not in collapse_graph:
            collapse_graph.add_node(departure, first_tx=find_creation_data(departure), points=0)
        collapse_graph.add_edge(departure, contract_address, value=int(transaction['value'])/10**18, hash=[transaction['hash']])
        one_layer_building(departure, collapse_graph)
    return collapse_graph

MINIMAL_LIFETIME = 30

def check_address_lifetime(start_date, collapse_graph):
    impostors = []
    dates = [re.sub(r'T.*', '', collapse_graph.nodes[node]["first_tx"]) for node in list(collapse_graph.nodes) if collapse_graph.nodes[node]['points'] >= 0]
    dates.sort()
    timestats = {date: 0 for date in dates}
    for node in collapse_graph.nodes:
        if collapse_graph.nodes[node]['points'] >= 0:
            timestats[re.sub(r'T.*', '', collapse_graph.nodes[node]["first_tx"])] += 1
        if (start_date - datetime.strptime(collapse_graph.nodes[node]["first_tx"], '%Y-%m-%dT%H:%M:%S') < timedelta(days=MINIMAL_LIFETIME)) and collapse_graph.nodes[node]['points'] >= 0:
            collapse_graph.nodes[node]['points'] += 1
            impostors.append(node)
    courses = [re.sub(r'202.-' , '', date) for date in list(timestats.keys())]
    values = list(timestats.values())  
    fig = plt.figure(figsize = (15, 5))
    plt.bar(courses, values, width = 0.5)
    plt.xlabel("Даты регистрации")
    plt.ylabel("Количество адресов")
    plt.title("Время регистрации адресов")
    plt.savefig('reg_time.jpg')
    return impostors

CRITICAL_IN_DEGREE_SHARE = 50

def check_address_connections(collapse_graph):
    impostors = []
    nodes_degrees = {node: collapse_graph.in_degree(node) for node in list(collapse_graph.nodes) if collapse_graph.nodes[node]['points'] >= 0}
    max_in_degree_node = max(nodes_degrees, key=nodes_degrees.get)
    impostors.append(max_in_degree_node)
    check_share = nodes_degrees[max_in_degree_node] / len(collapse_graph.nodes) * 100
    if check_share > CRITICAL_IN_DEGREE_SHARE:
        collapse_graph.nodes[max_in_degree_node]['points'] += 2
        for predecessor in collapse_graph.predecessors(max_in_degree_node):
            if collapse_graph.nodes[predecessor]['points'] >= 0:
                collapse_graph.nodes[predecessor]['points'] += 1
                impostors.append(predecessor)
    courses = []
    values = []
    for i in range(5):
        max_in_degree_node = max(nodes_degrees, key=nodes_degrees.get)
        courses.append(max_in_degree_node)
        values.append(nodes_degrees[max_in_degree_node])
        nodes_degrees.pop(max_in_degree_node)
    fig = plt.figure(figsize = (25, 10))
    plt.pie(values, labels=courses)
    plt.title("Связь с другими адресами")
    plt.savefig('connections.jpg')
    return impostors 

CRITICAL_TRANSACTIONS_PEAK_SHARE = 50

def check_transactions_peak(collapse_graph):
    impostors = []
    peak_date = {}
    for i, node in enumerate(collapse_graph.nodes):
        print(i, 'of' , len(collapse_graph.nodes))
        if collapse_graph.nodes[node]['points'] >= 0:
            txs_dates = [datetime.fromtimestamp(int(tx['timeStamp'])).strftime('%Y-%m-%d') for tx in get_txs_list(node)]
            diff_dates = set(txs_dates)
            dates_distribution = {d: txs_dates.count(d) for d in diff_dates}
            for date in dates_distribution:
                if dates_distribution[date] / len(txs_dates) * 100 > CRITICAL_TRANSACTIONS_PEAK_SHARE:
                    if date not in peak_date:
                        peak_date.update({date: []})
                    peak_date[date].append(node)
    max_peak_date = max(peak_date, key=lambda x: len(peak_date.get(x)))
    for node in peak_date[max_peak_date]:
        collapse_graph.nodes[node]['points'] += 1
        impostors.append(node)
    courses = [re.sub(r'202.-' , '', date) for date in list(peak_date.keys())]
    values = [len(node_list) for node_list in list(peak_date.values())]  
    fig = plt.figure(figsize = (15, 5))
    plt.bar(courses, values, width = 0.5)
    plt.xlabel("Даты проведения транзакций")
    plt.ylabel("Количество адресов")
    plt.title("Время пиков транзакций")
    plt.savefig('trxs_peak.jpg')
    return impostors

def save_graph_json(file_name, graph):
    with open(file_name, 'w') as graph_file:
        json.dump(networkx.node_link_data(graph), graph_file)

def wei_to_eth(collapse_graph):
    for edge in collapse_graph.edges:
        collapse_graph.edges[edge]['value'] = collapse_graph.edges[edge]['value'] / 10 ** 18

def save_graph_gexf(file_name, graph):
    networkx.set_edge_attributes(graph, values=0, name='hash')
    networkx.write_gexf(graph, 'collapse_graph.gexf')

def check_criterion(collapse_graph, start_date=datetime.now()):
    check_address_lifetime(start_date, collapse_graph)
    check_address_connections(collapse_graph)
    check_transactions_peak(collapse_graph)

if __name__ == '__main__':

    save_graph_json('not_crime_coll_graph.json', build_collapse_graph(ADDRESS))
    # with open('graph.json', 'r') as result_graph:
    #     graph = networkx.node_link_graph(json.load(result_graph))
    #     # please_kill_me_i_do_not_know_what_i_do(graph, datetime.strptime('Sep-10-2022 10:43:40 PM', '%b-%d-%Y %I:%M:%S %p'))
    #     # save_graph_json('graph.json', graph)
    #     # save_graph_gexf('collapse_graph.gexf', graph)

    print('done!')