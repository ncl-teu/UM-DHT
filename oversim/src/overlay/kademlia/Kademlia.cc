//
// Copyright (C) 2006 Institut fuer Telematik, Universitaet Karlsruhe (TH)
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

/**
 * @file Kademlia.cc
 * @author Sebastian Mies, Ingmar Baumgart, Bernhard Heep
 */

#include "Kademlia.h"
#include "KademliaMessage_m.h"

#include <assert.h>
#include <algorithm>

#include <IPAddressResolver.h>
#include <IPvXAddress.h>
#include <IInterfaceTable.h>
#include <IPv4InterfaceData.h>
#include "TopologyVis.h"
#include <AbstractLookup.h>
#include <LookupListener.h>
#include <RpcMacros.h>
#include <BootstrapList.h>
#include <string.h>
#include <cmath>
#include <iomanip>


#if 0
#define BUCKET_CONSISTENCY(msg) \
    do {\
        bool stFull = false;\
        int z = 0;\
        if (siblingTable != NULL && siblingTable->size() > 0) {\
            stFull = siblingTable->isFull();\
            z = routingBucketIndex(siblingTable->back().getKey()) - 1;\
            if (routingTable[z - 1] != NULL && routingTable[z - 1]->size())\
                breakpoint(#msg);\
        }\
        for (int y = 0; y < (z - 2); ++y) {\
            if ((routingTable[y] != NULL && routingTable[y]->size() > k) ||\
                (routingTable[y] != NULL && routingTable[y]->size() && !stFull))\
                breakpoint(#msg);\
        }\
    } while (false)
#else
#define BUCKET_CONSISTENCY(msg)
#endif

Define_Module(Kademlia);

std::ostream& operator<<(std::ostream& os, const KademliaBucket* n)
{
    if (n == NULL)
        os << "NULL";
    else {
        for (KademliaBucket::const_iterator i=n->begin(); i !=n->end(); i++) {
            os << *i << endl;
        }
        os << "last usage = " << n->getLastUsage();
    }
    return os;
};

class KademliaLookupListener : public LookupListener
{
private:
    Kademlia* overlay;
public:
    KademliaLookupListener(Kademlia* overlay)
    {
        this->overlay = overlay;
    }

    virtual void lookupFinished(AbstractLookup *lookup)
    {
        overlay->lookupFinished(lookup->isValid());
        delete this;
    }
};

//-----------------------------------------------------------------------------

void Kademlia::initializeOverlay(int stage)
{
    if (stage != MIN_STAGE_OVERLAY)
        return;

    // Kademlia provides KBR services
    kbr = true;

    // setup kademlia parameters
    minSiblingTableRefreshInterval = par("minSiblingTableRefreshInterval");
    minBucketRefreshInterval = par("minBucketRefreshInterval");
    siblingPingInterval = par("siblingPingInterval");
    exhaustiveRefresh = par("exhaustiveRefresh");
    maxStaleCount = par("maxStaleCount");
    pingNewSiblings = par("pingNewSiblings");
    enableReplacementCache = par("enableReplacementCache");
    replacementCachePing = par("replacementCachePing");
    replacementCandidates = par("replacementCandidates");
    secureMaintenance = par("secureMaintenance");
    newMaintenance = par("newMaintenance");

    //Threshold
    rtt_threshold = par("rtt_threshold");

    useEquSpace = par("useEquSpace");

    // R/Kademlia
    activePing = par("activePing");
    proximityRouting = par("proximityRouting");
    proximityNeighborSelection = par("proximityNeighborSelection");
    altRecMode = recordRoute = par("altRecMode");

    k = par("k");
    b = par("b");
    s = par("s");

    siblingRefreshNodes = par("siblingRefreshNodes");

    if (siblingRefreshNodes <= 0) {
        siblingRefreshNodes = 5 * s;
    }

    bucketRefreshNodes = par("bucketRefreshNodes");

    if (bucketRefreshNodes <= 0) {
        bucketRefreshNodes = iterativeLookupConfig.redundantNodes;
    }

    // calculate number of buckets: ( (2^b)-1 ) * ( keylength / b )
    numBuckets = ((1L << b) - 1L) * (OverlayKey::getLength() / b);

    // init routing and sibling table
    siblingTable = new KademliaBucket(s * 5, NULL);

    // initialize pointers
    routingTable.assign(numBuckets, (KademliaBucket*)NULL);

    WATCH_VECTOR(*siblingTable);
    WATCH_VECTOR(routingTable);

    // self-message
    bucketRefreshTimer = new cMessage("bucketRefreshTimer");
    siblingPingTimer = new cMessage("siblingPingTimer");

    // statistics
    bucketRefreshCount = 0;
    siblingTableRefreshCount = 0;
    nodesReplaced = 0;

    comparator = NULL;
}

Kademlia::Kademlia()
{
    siblingTable = NULL;
    comparator = NULL;
    bucketRefreshTimer = NULL;
    siblingPingTimer = NULL;
}

Kademlia::~Kademlia()
{
    routingDeinit();

    delete siblingTable;
    delete comparator;
    cancelAndDelete(bucketRefreshTimer);
    cancelAndDelete(siblingPingTimer);
}

void Kademlia::finishOverlay()
{
    simtime_t time = globalStatistics->calcMeasuredLifetime(creationTime);
    if (time < GlobalStatistics::MIN_MEASURED) return;

    globalStatistics->addStdDev("Kademlia: Nodes replaced in buckets/s",
                                nodesReplaced / time);
    globalStatistics->addStdDev("Kademlia: Bucket Refreshes/s",
                                bucketRefreshCount / time);
    globalStatistics->addStdDev("Kademlia: Sibling Table Refreshes/s",
                                siblingTableRefreshCount / time);
}

void Kademlia::sendSiblingFindNodeCall(const TransportAddress& dest)
{
    FindNodeCall* call = new FindNodeCall("FindNodeCall");
    call->setExhaustiveIterative(true);
    call->setLookupKey(thisNode.getKey());
    call->setNumRedundantNodes(siblingRefreshNodes);
    call->setNumSiblings(getMaxNumSiblings());
    call->setBitLength(FINDNODECALL_L(call));
    sendUdpRpcCall(dest, call);
}



void Kademlia::joinOverlay()
{
    // remove current node handle from the bootstrap list
    if (!thisNode.getKey().isUnspecified()) {
        bootstrapList->removeBootstrapNode(thisNode);
    }

    // initialize routing
    routingDeinit();
    routingInit();

    TransportAddress handle = bootstrapList->getBootstrapNode();

    if (!handle.isUnspecified()) {
        if (secureMaintenance) {
            sendSiblingFindNodeCall(handle);
        } else {
            // ping the bootstrap node to start bootstrapping
            pingNode(handle);
        }
    } else {
        // we're the only node in the network
        state = READY;
        setOverlayReady(true);

        // schedule bucket refresh timer
        cancelEvent(bucketRefreshTimer);
        scheduleAt(simTime(), bucketRefreshTimer);
        cancelEvent(siblingPingTimer);
        scheduleAt(simTime() + siblingPingInterval, siblingPingTimer);
    }
}

//-----------------------------------------------------------------------------

void Kademlia::routingInit()
{
    // set join state
    state = INIT;

    setOverlayReady(false);

    // setup comparator
    comparator = new KeyDistanceComparator<KeyXorMetric>(thisNode.getKey());

    siblingTable->setComparator(comparator);

    updateTooltip();
    BUCKET_CONSISTENCY(routingInit: end);
}

void Kademlia::routingDeinit()
{
    // delete buckets
    for (uint32_t i = 0; i < routingTable.size(); i++) {
        if (routingTable[i] != NULL) {
            delete routingTable[i];
            routingTable[i] = NULL;
        }
    }

    if (siblingTable != NULL) {
        siblingTable->clear();
    }

    if (comparator != NULL) {
        delete comparator;
        comparator = NULL;
    }
}

int Kademlia::getMaxNumSiblings()
{
    return s;
}

int Kademlia::getMaxNumRedundantNodes()
{
    return k;
}

int Kademlia::routingBucketIndex(const OverlayKey& key, bool firstOnLayer)
{
    // calculate XOR distance
    OverlayKey delta = key ^ getThisNode().getKey();

    // find first subinteger that is not zero...
    int i;
    for (i = key.getLength() - b; i >= 0 && delta.getBitRange(i, b) == 0;
         i -= b);

    if (i < 0)
        return -1;

    if (!firstOnLayer)
        return (i / b) * ((1 << b) - 1) + (delta.getBitRange(i, b) - 1);
    else
        return (i / b) * ((1 << b) - 1) + (pow(2, b) - 2);
}

KademliaBucket* Kademlia::routingBucket(const OverlayKey& key, bool ensure)
{
    // get bucket index
    int num = routingBucketIndex(key);
    if (num < 0)
        return NULL;

    // get bucket and allocate if necessary
    KademliaBucket* bucket = routingTable[ num ];
    if (bucket == NULL && ensure)
        bucket = routingTable[ num ] = new KademliaBucket( k, comparator );

    // return bucket
    return bucket;
}

//Added by Kanemitsu START
/**
 * 分散を求める．
 * @param list
 * @param handle
 * @param target
 * @return
 */
long double Kademlia::calcDistanceV(KademliaBucket& list, OverlayKey tKey){
    int cnt = 0;
    int64_t totalDistance = 0;
    OverlayKey predKey;
    for(KademliaBucket::iterator p_a=list.begin(); p_a!=list.end();p_a++){
        // for(std::vector<KademliaBucketEntry>::iterator p_a=list.begin(); p_a!=list.end();p_a++){
        if(p_a->getKey() == tKey){
            continue;
        }
        if(cnt == 0){
            //k-bucketの最初の端の値を取得する．
            //predKey = orgKeyVector.begin().getKey();
            cnt++;
        }else{
            if(!p_a->isUnspecified() && !predKey.isUnspecified()){
                totalDistance += KeyPrefixMetric().distance2(p_a->getKey(), predKey);
                cnt++;
            }


        }
        predKey = p_a->getKey();
        // cnt++;
    }
    if(!list[list.size()-1].isUnspecified() && !predKey.isUnspecified()){
        //最後の距離を求める．
        totalDistance += KeyPrefixMetric().distance2(list[list.size()-1].getKey(), predKey);
    }

    //オリジナルの平均を求める．
    int64_t ave_orgDistance = totalDistance / cnt;
    //オリジナルの分散を求める．
    cnt = 0;
    long double total_orgv = 0;
    for(KademliaBucket::iterator p_b=list.begin(); p_b!=list.end();p_b++){
        //for(std::vector<KademliaBucketEntry>::iterator p_b=list.begin(); p_b!=list.end();p_b++){
        if(cnt == 0){
            //k-bucketの最初の端の値を取得する．
            //predKey = startEdgeKey;
            cnt++;
        }else{
            if(!p_b->isUnspecified() && !predKey.isUnspecified()){
                int64_t dist = KeyPrefixMetric().distance2(p_b->getKey(), predKey);
                total_orgv  += abs(dist - ave_orgDistance) * abs(dist - ave_orgDistance);
                cnt++;
            }

        }
        predKey = p_b->getKey();

    }
    if(!list[list.size()-1].isUnspecified() && !predKey.isUnspecified()) {
        total_orgv += KeyPrefixMetric().distance2(list[list.size()-1].getKey(), predKey);

    }
    //オリジナルの分散を求める．
    long double v_orgDistance = total_orgv / cnt;

    return v_orgDistance;
}



KademliaBucketEntry* Kademlia::getTarget(std::vector<KademliaBucketEntry>& list, KademliaBucketEntry& handle){
    return NULL;
}
//Added by Kanemitsu END

bool Kademlia::routingAdd(const NodeHandle& handle, bool isAlive,
                          simtime_t rtt, bool maintenanceLookup)
{


    BUCKET_CONSISTENCY(routingAdd: start);
    // never add unspecified node handles
    if (handle.isUnspecified() || handle.getKey() == getThisNode().getKey()) {
        return false;
    }

    EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
       << " (" << thisNode.getKey().toString(16) << ")]\n"
       << "    inserting node " << handle << " (rtt = ";
    if (rtt == MAXTIME) {
        EV << "<unknown>";
    } else {
        EV << SIMTIME_DBL(rtt);
    }
    EV << ", isAlive = " << (isAlive?"true":"false")
       << ") ..." << endl;

    // bucket index
    KademliaBucket::iterator i;
    bool result = false;
    bool authenticated = (isAlive && (rtt != MAXTIME));

    bool needsRtt = (activePing && ((rtt == MAXTIME) ? true : false));

    // convert node handle
    KademliaBucketEntry kadHandle = handle;
    kadHandle.setRtt(rtt);
    kadHandle.setLastSeen(simTime());

    /* check if node is already a sibling -----------------------------------*/
    if ((i = siblingTable->findIterator(kadHandle.getKey()))
        != siblingTable->end()) {
        // not alive? -> do not change routing information
        if (isAlive) {
            if (!secureMaintenance || authenticated) {
                if (kadHandle.getRtt() == MAXTIME) {
                    kadHandle.setRtt(i->getRtt());
                }
                // refresh sibling
                (*i) = kadHandle;
            } else {
                if (maintenanceLookup) {
                    return false;
                }

                if ((i->getIp() != kadHandle.getIp()) ||
                    (i->getPort() != kadHandle.getPort())) {
                    // sibling could have changed transport address
                    // ping new address for authentication
                    pingNode(kadHandle);
                    return false;
                }
            }
        }
        BUCKET_CONSISTENCY(routingAdd: node is sibling);
        EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
           << " (" << thisNode.getKey().toString(16) << ")]\n"
           << "    ... node is already in the sibling table." << endl;
        return true;
    }

    /* check if node is already in a bucket ---------------------------------*/
    KademliaBucket* bucket = routingBucket(kadHandle.getKey(), false);
    if (bucket != NULL && (i = bucket->findIterator(kadHandle.getKey() ) )
                          != bucket->end() ) {
        // not alive? -> do not change routing information
        if (isAlive) {
            if (!secureMaintenance || authenticated) {
                if (kadHandle.getRtt() == MAXTIME) {
                    kadHandle.setRtt(i->getRtt());
                }

                // R/Kademlia
                if (needsRtt && (kadHandle.getRtt() == MAXTIME)) {
                    Prox prox =
                            neighborCache->getProx(kadHandle, NEIGHBORCACHE_DEFAULT, -1,
                                                   this, NULL);
                    if (prox != Prox::PROX_SELF &&
                        prox != Prox::PROX_UNKNOWN &&
                        prox != Prox::PROX_WAITING &&
                        prox != Prox::PROX_TIMEOUT) {
                        kadHandle.setProx(prox);
                        //routingAdd(handle, true, prox.proximity);//ctrlInfo->getSrcRoute() //TODO
                    } /*else if (prox == Prox::PROX_TIMEOUT) {
                        // remove from bucket
                        bucket->erase(i);
                        return false;
                    }*/ //TODO inform NC that node is alive
                    else {
                        EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
                           << " (" << thisNode.getKey().toString(16) << ")]\n"
                                                                        "    ... node not added, but ping sent." << endl;
                        return false;
                    }
                }

                // remove old handle
                bucket->erase(i);
                // re-add to tail
                bucket->push_back(kadHandle);
            } else {
                if (maintenanceLookup) {
                    return false;
                }

                if ((i->getIp() != kadHandle.getIp()) ||
                    (i->getPort() != kadHandle.getPort())) {
                    // sibling could have changed transport address
                    // ping new address for authentication
                    pingNode(kadHandle);
                    return false;
                }
            }
        }
        BUCKET_CONSISTENCY(routingAdd: node is in bucket);
        EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
           << " (" << thisNode.getKey().toString(16) << ")]\n"
           << "    ... node is already in bucket "
           << routingBucketIndex(kadHandle.getKey()) << "." << endl;
        return true;
    }

    /* check if node can be added to the sibling list -----------------------*/
    if (siblingTable->isAddable(kadHandle) ) {
        if (secureMaintenance && !authenticated) {
            if (!maintenanceLookup || (isAlive && (rtt == MAXTIME))) {
                // received a FindNodeCall or PingCall from a potential sibling
                // or new nodes from a FindNodeResponse app lookup
                pingNode(kadHandle);
            } else if (newMaintenance) {
                // new node from sibling table refresh
                //sendSiblingFindNodeCall(kadHandle);
                pingNode(kadHandle);
            }
            return false;
        }

        // ping new siblings
        if (pingNewSiblings && !isAlive) {
            pingNode(kadHandle);
        }

            // R/Kademlia
        else if (needsRtt) {
            // old version: pingNode(), now:
            Prox prox =
                    neighborCache->getProx(kadHandle, NEIGHBORCACHE_DEFAULT, -1,
                                           this, NULL);
            if (prox != Prox::PROX_SELF &&
                prox != Prox::PROX_UNKNOWN &&
                prox != Prox::PROX_TIMEOUT) {
                kadHandle.setProx(prox);
            } else if (prox == Prox::PROX_TIMEOUT) {
                // do not put handle into sibling table
                EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
                   << " (" << thisNode.getKey().toString(16) << ")]\n"
                   << "    ... node not added (node timeout)." << endl;
                return false;
            }
        }

        bool finished = false;
        int siblingPos = -1;
        //EV << "***KETA:" <<KeyPrefixMetric().distance(kadHandle.getKey(), thisNode.getKey()) << endl;

        // check if sibling list is full so a handle is preemted from the list
        if (siblingTable->isFull()) {
            // get handle thats about to be preempted
            KademliaBucketEntry oldHandle = siblingTable->back();
            assert(oldHandle.getKey() != kadHandle.getKey());

            // add handle to the sibling list
            siblingPos = siblingTable->add(kadHandle);
            EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
               << " (" << thisNode.getKey().toString(16) << ")]\n"
               << "    ... node added to sibling table, replacing "
               << (NodeHandle)oldHandle << endl;

            // change, so that the preempted handle is added to a bucket
            kadHandle = oldHandle;

            // call update() for removed sibling
            if (!secureMaintenance) {
                deleteOverlayNeighborArrow(oldHandle);
                callUpdate(oldHandle, false);
            }

            // return always true, since the handle has been added
            result = true;
        } else {
            // simply add the handle and stop
            siblingPos = siblingTable->add(kadHandle);
            EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
               << " (" << thisNode.getKey().toString(16) << ")]\n"
               << "    ... node added to sibling table." << endl;

            // don't need to add kadHandle also to regular buckets
            finished = true;
        }
        assert(siblingPos > -1);

        updateTooltip();

        // call update() for new sibling
        showOverlayNeighborArrow(siblingTable->at(siblingPos), false,
                                 "m=m,50,100,50,100;ls=green,1");
        callUpdate(siblingTable->at(siblingPos), true);

        if (finished) {
            BUCKET_CONSISTENCY(routingAdd: node is now sibling);
            return true;
        }
    }

    /* add node to the appropriate bucket, if not full ---------------------*/
    bucket = routingBucket(kadHandle.getKey(), true);
    if (!bucket->isFull()) {
        if (secureMaintenance && !authenticated) {
            if (/*!maintenanceLookup || */(isAlive && (rtt == MAXTIME))) {
                // received a FindNodeCall or PingCall from a potential new bucket entry
                // or new nodes from a FindNodeReponse app lookup
                // optimization: don't send a ping for nodes from FindNodeResponse for app lookups
                pingNode(kadHandle);
            }
            return false;
        }

        //EV << "[Kademlia::routingAdd()]\n"
        //   << "    Adding new node " << kadHandle
        //   << " to bucket " << routingBucketIndex(kadHandle.getKey())
        //   << endl;

        // PNS
        if (needsRtt || proximityNeighborSelection) {
            //pingNode(handle, -1, 0, NULL, NULL, NULL, -1, UDP_TRANSPORT, false);
            Prox prox =
                    neighborCache->getProx(kadHandle, NEIGHBORCACHE_DEFAULT, -1,
                                           this, NULL);
            if (prox != Prox::PROX_SELF &&
                prox != Prox::PROX_UNKNOWN &&
                prox != Prox::PROX_TIMEOUT) {
                //routingAdd(handle, true, prox.proximity);//ctrlInfo->getSrcRoute() //TODO
                kadHandle.setProx(prox);
            }
        }

        bucket->push_back(kadHandle);
        result = true;
        EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
           << " (" << thisNode.getKey().toString(16) << ")]\n"
           << "    ... node added to bucket "
           << routingBucketIndex(kadHandle.getKey())
           << " which was not yet full." << endl;
    } else if (isAlive) {
        bool isHandleAdded = false;
//Added by Kanemitsu START
        if((rtt_threshold > 0)&&(!kadHandle.isUnspecified())){
            //k-bucket内の隣り合うID間の距離を求める．
            //そして，その平均値を求めて，その分散が最小になるようにする．

            if(useEquSpace){
                if(kadHandle.getRtt() == MAXTIME){
                    Prox prox =
                            neighborCache->getProx(kadHandle, NEIGHBORCACHE_DEFAULT, -1,
                                                   this, NULL);
                    if (prox != Prox::PROX_SELF &&
                        prox != Prox::PROX_UNKNOWN &&
                        prox != Prox::PROX_WAITING &&
                        prox != Prox::PROX_TIMEOUT) {
                        kadHandle.setProx(prox);
                        //routingAdd(handle, true, prox.proximity);//ctrlInfo->getSrcRoute() //TODO
                    }
                }
                int idx = routingBucketIndex(kadHandle.getKey());
                //int32_t startEdge = pow(2, idx);
                // OverlayKey startEdgeKey = new OverlayKey(startEdge);
                // int32_t endEdge = pow(2, idx +1);

                // OverlayKey endEdgeKey = new OverleyKey(endEdge);
/*
                std::vector<KademliaBucketEntry> keyVector;
                std::vector<KademliaBucketEntry> orgKeyVector;
                std::vector<KademliaBucketEntry> rttVector;
*/
                KademliaBucket keyVector;
                KademliaBucket orgKeyVector;
                KademliaBucket rttVector;

                keyVector.push_back(kadHandle);
                for(KademliaBucket::iterator v=bucket->begin(); v!=bucket->end();v++){
                    if(v->isUnspecified()){
                        continue;
                    }
                    keyVector.push_back(*v);
                    orgKeyVector.push_back(*v);


                }

                //IDの小さい順にソートする．
                std::sort(orgKeyVector.begin(), orgKeyVector.end(), CompKey());

                OverlayKey predKey;
                //オリジナルの場合の分散を計算する．
                //まずは平均値
                int cnt = 0;
                int64_t  totalDistance = 0;

                for(KademliaBucket::iterator p_a=orgKeyVector.begin(); p_a!=orgKeyVector.end();p_a++){
                    // for(std::vector<KademliaBucketEntry>::iterator p_a=orgKeyVector.begin(); p_a!=orgKeyVector.end();p_a++){
                    if(cnt == 0){
                        //k-bucketの最初の端の値を取得する．
                        //predKey = orgKeyVector.begin().getKey();
                        cnt++;
                    }else{
                        if(!p_a->isUnspecified() && !predKey.isUnspecified()){
                            totalDistance += KeyPrefixMetric().distance2(p_a->getKey(), predKey);
                            cnt++;
                        }



                    }
                    predKey = p_a->getKey();
                }
                //最後の距離を求める．
                if(!orgKeyVector[orgKeyVector.size()-1].isUnspecified() && !predKey.isUnspecified()){
                    totalDistance += KeyPrefixMetric().distance2(orgKeyVector[orgKeyVector.size()-1].getKey(), predKey);

                }
                //オリジナルの平均を求める．
                int64_t  ave_orgDistance = totalDistance / cnt;
                //int64_t  ave_orgDistance = fixed<<std::setprecision(4) << totalDistance/cnt;

                //オリジナルの分散を求める．
                cnt = 0;
                long double total_orgv = 0;
                for(KademliaBucket::iterator p_b=orgKeyVector.begin(); p_b!=orgKeyVector.end();p_b++){
                    //for(std::vector<KademliaBucketEntry>::iterator p_b=orgKeyVector.begin(); p_b!=orgKeyVector.end();p_b++){
                    if(cnt == 0){
                        //k-bucketの最初の端の値を取得する．
                        //predKey = startEdgeKey;
                        cnt++;
                    }else{
                        if(!p_b->isUnspecified() && !predKey.isUnspecified()){
                            int64_t  dist = KeyPrefixMetric().distance2(p_b->getKey(), predKey);
                            total_orgv  += abs(dist - ave_orgDistance) * abs(dist - ave_orgDistance);
                            cnt++;
                        }

                    }
                    predKey = p_b->getKey();


                }
                if(!orgKeyVector[orgKeyVector.size()-1].isUnspecified() && !predKey.isUnspecified()) {
                    total_orgv += KeyPrefixMetric().distance2(orgKeyVector[orgKeyVector.size()-1].getKey(), predKey);

                }
                //オリジナルの分散を求める．
                long double v_orgDistance = total_orgv / cnt;

                cnt = 0;
                for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                    //もしnewEntryよりもRTTが大きなものがいれば，対象に入れる．
                    if(j->getRtt() >= kadHandle.getRtt()){
                        rttVector.push_back(*j);
                    }
                    cnt++;
                }
                if(bucket->end()->getRtt() >= kadHandle.getRtt()){
                    rttVector.push_back(*bucket->end());
                }
                //次は，kadhandleと，rttVectorどれか一つを入れ替えた場合の分散を求める．
                //そのために毎回，vectorを生成する．
                //keyの小さい順にソートする．
                //keyVector.push_back(kadHandle);
                std::sort(keyVector.begin(), keyVector.end(), CompKey());
                int64_t  minV = v_orgDistance;
                bool found = false;
                //vectorの最初から見る．
                KademliaBucket::iterator retEntry;
                for(KademliaBucket::iterator p_c=rttVector.begin(); p_c!=rttVector.end();p_c++){
                    // for(std::vector<KademliaBucketEntry>::iterator p_c=rttVector.begin(); p_c!=rttVector.end();p_c++){
                    if(*p_c == kadHandle){
                        continue;
                    }
                    //keyVector.erase(p_c);
                    //p_aをターゲットとする．
                    //keyVectorからp_cを削除して，その分散を求める．
                    //入力としては，keyVectorとなる．
                    //その後，keyVectorにp_cをpush_backしてsortする．

                    long double tmpV = this->calcDistanceV(keyVector, p_c->getKey());

                    if(tmpV <= minV){
                        minV = tmpV;
                        retEntry = p_c;
                        found = true;

                    }
                    //keyVector.push_back(*p_c);
                    //std::sort(keyVector.begin(), keyVector.end(), CompKey());

                }

                if(found){
                    for(KademliaBucket::iterator m=bucket->begin(); m!=bucket->end();m++){
                        if(retEntry->getKey() == m->getKey()){
                            bucket->erase(m);
                            break;
                        }
                    }

                    //bucket->erase(retEntry);
                    //re-add to tail
                    bucket->push_back(kadHandle);
                    isHandleAdded = true;

                }else{

                }


            }else{

                //OverlayKey totalKey = 0;
                double init_total = 0;
                std::vector<KademliaBucketEntry> largeRTTVector;
                if(kadHandle.getRtt() == MAXTIME){
                    Prox prox =
                            neighborCache->getProx(kadHandle, NEIGHBORCACHE_DEFAULT, -1,
                                                   this, NULL);
                    if (prox != Prox::PROX_SELF &&
                        prox != Prox::PROX_UNKNOWN &&
                        prox != Prox::PROX_WAITING &&
                        prox != Prox::PROX_TIMEOUT) {
                        kadHandle.setProx(prox);
                        //routingAdd(handle, true, prox.proximity);//ctrlInfo->getSrcRoute() //TODO
                    }
                }
                //平均値を求めるためのループ
                for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                    //totalKey += j->getKey();
                    // init_total += (thisNode.getKey()^(j->getKey())).toDouble();

                    init_total += KeyPrefixMetric().distance2(bucket->begin()->getKey(), j->getKey());
                    //EV << "KETA1:"<< (thisNode.getKey()^(j->getKey())).toDouble() <<endl;
                    if(j->getRtt() == MAXTIME){
                        //continue;
                    }
                    if(j->getRtt() >= kadHandle.getRtt()){
                        //   largeRTTVector.push_back(*j);
                    }

                }
                //std::sort(largeRTTVector.begin(), largeRTTVector.end(),CompDec());


                //kadhandleとvectorの各要素を取り替えることで，keyの分散が大きくなれば良し．
                //現状の平均値
                //double init_total = totalKey.toDouble();
                double init_total2 = init_total;
                double init_ave = init_total/bucket->size();
                double tmp_total = 0;
                //初期の分散を求めるためのループ
                for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                    double tmp = KeyPrefixMetric().distance2(bucket->begin()->getKey(), j->getKey());
                    tmp_total += abs(tmp-init_ave) * abs(tmp-init_ave);

                }

                double max_d2 = tmp_total / bucket->size();
                double h_val = 0;
                bool found = false;
                //KademliaBucketEntry target;
                KademliaBucket::iterator target;
                KademliaBucket target2;

                //最大の分散を求めるためのループ
                // for(std::vector<KademliaBucketEntry>::iterator j=largeRTTVector.begin(); j!=largeRTTVector.end();j++){
                for(KademliaBucket::iterator j=bucket->begin(); j!=bucket->end();j++){
                    if(j->getRtt() < kadHandle.getRtt()){
                        continue;
                    }

                    //target = j;
                    // if(largeRTTVector.
                    //jの値
                    uint32_t val = KeyPrefixMetric().distance2(bucket->begin()->getKey(), j->getKey());

                    uint32_t kadVal = KeyPrefixMetric().distance2(bucket->begin()->getKey(), kadHandle.getKey());
                    double  total = init_total - val + kadVal;
                    //jとkadHandleを交換した場合の平均．
                    double  ave = total / bucket->size();
                    //kadHandleの要素値
                    double k_val = abs(kadVal - ave)*abs(kadVal - ave);
                    //     double k_val = 1;
                    uint32_t d_total = k_val;
                    //jをkadHandleを交換した場合の分散を求めるためのループ
                    // for(std::vector<KademliaBucketEntry>::iterator m=largeRTTVector.begin(); m!=largeRTTVector.end();m++){
                    for(KademliaBucket::iterator m=bucket->begin(); m!=bucket->end();m++){
                        //mの要素の値
                        double val2 = KeyPrefixMetric().distance2(bucket->begin()->getKey(), m->getKey());
                        //jの値 = mの値だと，mが交換対象なので考えない．
                        if(val2 == val){
                            continue;
                        }else{
                            double dif = abs(val2 - ave) * abs(val2 - ave);
                            //double dif = 0;
                            d_total += dif;
                        }

                    }


                    // }
                    double  d = d_total / bucket->size();
                    if(max_d2 <= d){
                        found = true;

                        max_d2 = d;
                        target = j;
                    }
                    init_total = init_total2;
                }

                if(found){
                    bucket->erase(target);
                    //re-add to tail
                    bucket->push_back(kadHandle);

                }
            }


        }
//Added by Kanemitsu END
        //PNS node replacement
        if (proximityNeighborSelection &&
            kadHandle.getProx() != Prox::PROX_UNKNOWN) {
            KademliaBucket::iterator kickHim, it;
            kickHim = it = bucket->begin();
            ++it;
            while (it != bucket->end()) {
                if (it->getRtt() > kickHim->getRtt()) {
                    kickHim = it;
                }
                ++it;
            }
            if (kickHim->getRtt() > kadHandle.getRtt()) {
                KademliaBucketEntry temp = *kickHim;
                bucket->erase(kickHim);
                if(!isHandleAdded){
                    bucket->push_back(kadHandle);

                }
                kadHandle = temp;
                EV << "[Kademlia::routingAdd()] @ " << thisNode.getIp()
                   << " (" << thisNode.getKey().toString(16) << ")]\n"
                   << "    ... added to bucket "
                   << routingBucketIndex(kadHandle.getKey())
                   << " (PNS: replacing another node)." << endl;
            }
        }

        if (enableReplacementCache && (!secureMaintenance || authenticated)) {
            bucket->replacementCache.push_front(kadHandle);
            if (bucket->replacementCache.size() > replacementCandidates) {
                bucket->replacementCache.pop_back();
            }

            if (replacementCachePing) {
                KademliaBucket::iterator it = bucket->begin();
                while (it != bucket->end() && (it->getPingSent() == true)) {
                    it++;
                }
                if (it != bucket->end()) {
                    pingNode(*it);
                    it->setPingSent(true);
                }
            }
        }
    }

        // PNS
    else if (proximityNeighborSelection) {
        neighborCache->getProx(kadHandle, NEIGHBORCACHE_QUERY, -1, this, NULL);
        //pingNode(kadHandle);
    }

    BUCKET_CONSISTENCY(routingAdd: end);
    return result;
}

bool Kademlia::routingTimeout(const OverlayKey& key, bool immediately)
{
    BUCKET_CONSISTENCY(routingTimeout: start);
    // key unspecified? yes -> ignore
    if (key.isUnspecified())
        return false;

    // bucket index
    KademliaBucket::iterator i;

    /* check if the node is one of the siblings -----------------------------*/
    if ((i = siblingTable->findIterator(key)) != siblingTable->end()) {

        i->incStaleCount();
        i->setPingSent(false);

        if (i->getStaleCount() > maxStaleCount || immediately) {
            // remove from sibling table
            NodeHandle oldSibling = *i;
            siblingTable->erase(i);

            // lost last sibling?
            if (siblingTable->size() == 0) {
                join();
                return true;
            }

            BUCKET_CONSISTENCY(routingTimeout: is sibling);

            // try to refill with new closest contact
            refillSiblingTable();

            // call update() for removed sibling
            deleteOverlayNeighborArrow(oldSibling);
            callUpdate(oldSibling, false);

            updateTooltip();

            return true;
        }
    }

    /* check if node is already in a bucket ---------------------------------*/
    KademliaBucket* bucket = routingBucket(key, false);
    if (bucket != NULL && (i = bucket->findIterator(key) ) != bucket->end() ) {

        i->incStaleCount();
        i->setPingSent(false);

        if (i->getStaleCount() > maxStaleCount || immediately) {
            // remove from routing table
            bucket->erase(i);

            if (enableReplacementCache) {
                if (bucket->replacementCache.size()) {
                    routingAdd(bucket->replacementCache.front(), true,
                               bucket->replacementCache.front().getRtt());
                    bucket->replacementCache.pop_front();
                    nodesReplaced++;
                }
            }
        }

        BUCKET_CONSISTENCY(routingTimeout: is in bucket);
        return true;
    }
    BUCKET_CONSISTENCY(routingTimeout: end);
    return false;
}

void Kademlia::refillSiblingTable()
{
    if (siblingTable->size() == 0 ||
        siblingTable->isFull())
        return;

    int index = routingBucketIndex(siblingTable->back().getKey()) - 1;
    assert(index > 0);

    while ((routingTable[index] == NULL ||
            routingTable[index]->empty()) &&
           index < (int)(OverlayKey::getLength() - 1)) {
        index++;
    }
    if (index < (int)OverlayKey::getLength() &&
        routingTable[index] != NULL && routingTable[index]->size()) {

        KademliaBucket sortedBucket(k, comparator);
        for (uint32_t i = 0; i < routingTable[index]->size(); ++i) {
            sortedBucket.add(routingTable[index]->at(i));
        }

        siblingTable->add(sortedBucket.front());

        // call update() for new sibling
        if (!secureMaintenance) {
            showOverlayNeighborArrow(sortedBucket.front(), false,
                                     "m=m,50,100,50,100;ls=green,1");
            callUpdate(sortedBucket.front(), true);
        }

        // remove node from bucket
        routingTable[index]->erase(routingTable[index]->
                findIterator(sortedBucket.front().getKey()));
        assert(siblingTable->isFull());
        BUCKET_CONSISTENCY(routingTimeout: end refillSiblingTable());
    }
}

void Kademlia::setBucketUsage(const OverlayKey& key)
{
    KademliaBucket* bucket = routingBucket(key, true);

    if (bucket) {
        bucket->setLastUsage(simTime());
    }

    if ((siblingTable->size() < (uint32_t)getMaxNumSiblings())
        || ((siblingTable->at(getMaxNumSiblings() - 1).getKey() ^ thisNode.getKey())
            >= (key ^ thisNode.getKey()))) {
        siblingTable->setLastUsage(simTime());
    }

}

bool Kademlia::isSiblingFor(const NodeHandle& node, const OverlayKey& key,
                            int numSiblings, bool* err)
{
    if (key.isUnspecified())
        error("Kademlia::isSiblingFor(): key is unspecified!");

    if (state != READY) {
        EV << "[Kademlia::isSiblingFor()] @ "
           << thisNode.getIp()
           << " (" << thisNode.getKey().toString(16) << ")]\n"
           << "    state != READY"
           << endl;
        *err = true;
        return false;
    }

    if (numSiblings > getMaxNumSiblings()) {
        opp_error("Kademlia::isSiblingFor(): numSiblings too big!");
    }

    // set default number of siblings to consider
    if (numSiblings == -1) {
        numSiblings = getMaxNumSiblings();
    }

    if (numSiblings == 0) {
        *err = false;
        return (node.getKey() == key);
    }

    if (siblingTable->size() < (uint)numSiblings) {
        *err = false;
        return true;
    }

    if (siblingTable->isFull() &&
        ((thisNode.getKey() ^ key) >
         (thisNode.getKey() ^ siblingTable->back().getKey()))) {
        EV << "[Kademlia::isSiblingFor()] @ "
           << thisNode.getIp()
           << " (" << thisNode.getKey().toString(16) << ")]\n"
           << "    Not sure if I am sibling for " << key << " !\n"
           << "    (" << key << " is not closer to me than "
           << siblingTable->back().getKey() << ")"
           << endl;
        *err = true;
        return false;
    }

    KeyDistanceComparator<KeyXorMetric>* comp =
            new KeyDistanceComparator<KeyXorMetric>(key);

    // create result vector
    NodeVector* result = new NodeVector(numSiblings, comp);

    for (KademliaBucket::iterator i=siblingTable->begin();
         i != siblingTable->end(); i++) {
        result->add( *i);
    }

    // add local node
    result->add(thisNode);

    *err = false;
    delete comp;

    if (result->contains(node.getKey())) {
        delete result;
        return true;
    } else {
        delete result;
        assert(!(numSiblings == 1 && key == node.getKey()));
        return false;
    }
}

void Kademlia::handleNodeGracefulLeaveNotification()
{
    // send failed node call to all siblings
    FailedNodeCall* call = new FailedNodeCall();
    call->setFailedNode(getThisNode());
    call->setBitLength(FAILEDNODECALL_L(call));
    for (KademliaBucket::iterator i = siblingTable->begin();
         i != siblingTable->end(); i++) {
        countFailedNodeCall(call);
        sendUdpRpcCall(*i, call->dup());
    }

    delete call;
}

bool Kademlia::handleFailedNode(const TransportAddress& failed)
{
    assert(!failed.isUnspecified());

    KademliaBucket::iterator i;
    // check sibling table
    for (i = siblingTable->begin(); i != siblingTable->end(); ++i) {
        if (failed == *i) break;
    }

    if (i != siblingTable->end()) {
        // remove from sibling table
        NodeHandle oldSibling = *i;
        siblingTable->erase(i);

        // call update() for removed sibling
        deleteOverlayNeighborArrow(oldSibling);
        callUpdate(oldSibling, false);

        updateTooltip();

        // try to refill with new closest contact
        refillSiblingTable();
    } else {
        // check buckets
        uint32_t m;
        for (m = 0; m < routingTable.size(); ++m) {
            if (routingTable[m] != NULL) {
                for (i = routingTable[m]->begin(); i != routingTable[m]->end();
                     ++i) {
                    if (failed == *i) {
                        // remove from routing table
                        routingTable[m]->erase(i);
                        return (siblingTable->size() != 0);
                    }
                }
            }
        }
    }
    return (siblingTable->size() != 0);
}

// R/Kademlia
bool Kademlia::recursiveRoutingHook(const TransportAddress& dest,
                                    BaseRouteMessage* msg)
{
    if (msg->getSrcNode() != thisNode) {
        if (!msg->getDestKey().isUnspecified()) {
            routingAdd(msg->getSrcNode(), true);

            if (altRecMode && dest != thisNode) return true;

            NodeVector* nextHops = findNode(msg->getDestKey(), /*recursiveLookupConfig.redundantNodes*/ k, s, msg);
            KademliaRoutingInfoMessage* kadRoutingInfoMsg =
                    new KademliaRoutingInfoMessage();

            kadRoutingInfoMsg->setSrcNode(thisNode);
            kadRoutingInfoMsg->setDestKey(msg->getDestKey());
            kadRoutingInfoMsg->setNextHopsArraySize(nextHops->size());
            kadRoutingInfoMsg->setName("KadRoutingInfoMsg");
            for (uint32_t i = 0; i < nextHops->size(); i++) {
                kadRoutingInfoMsg->setNextHops(i, (*nextHops)[i]);
                if (thisNode == kadRoutingInfoMsg->getNextHops(i)) {
                    kadRoutingInfoMsg->getNextHops(i).setIsAlive(true);
                }
            }
            kadRoutingInfoMsg->setBitLength(KADEMLIAROUTINGINFO_L(kadRoutingInfoMsg));

            delete nextHops;

            if (!altRecMode) {
                sendMessageToUDP(msg->getSrcNode(), kadRoutingInfoMsg, 0.000001);
            } else {
                // alternative maintenance mode
                std::vector<TransportAddress> sourceRoute;
                for (int i = msg->getVisitedHopsArraySize() - 1/*2*/; i >= 0; i--) {
                    //TODO remove loops
                    sourceRoute.push_back(msg->getVisitedHops(i));
                }
                //sourceRoute.push_back(msg->getSrcNode());
                sendToKey(OverlayKey::UNSPECIFIED_KEY, kadRoutingInfoMsg, 0,
                          sourceRoute, NO_OVERLAY_ROUTING);
            }
            //TODO should be sent after baseroutemsg
        } else if (altRecMode &&
                   dynamic_cast<KademliaRoutingInfoMessage*>(msg->
                           getEncapsulatedPacket())) {
            // alternative mode: infoMsg on its way back
            KademliaRoutingInfoMessage* infoMsg =
                    static_cast<KademliaRoutingInfoMessage*>(msg->decapsulate());
            NodeVector* nextHops = findNode(infoMsg->getDestKey(), k, s, msg);

            // merge vectors
            KeyDistanceComparator<KeyXorMetric> comp(infoMsg->getDestKey());
            MarkedNodeVector temp(UINT16_MAX, &comp);

            for (uint32_t i = 0; i < nextHops->size(); i++) {
                temp.push_back((*nextHops)[i]);
            }
            delete nextHops;

            for (uint32_t i = 0; i < infoMsg->getNextHopsArraySize(); i++) {
                routingAdd(infoMsg->getNextHops(i),
                           infoMsg->getNextHops(i).getIsAlive());
                temp.add(infoMsg->getNextHops(i));
            }

            infoMsg->setNextHopsArraySize(temp.size());
            for (uint32_t i = 0; i < temp.size(); ++i) {
                infoMsg->setNextHops(i, temp[i]);
                if (thisNode == infoMsg->getNextHops(i)) {
                    infoMsg->getNextHops(i).setIsAlive(true);
                }
            }
            infoMsg->setBitLength(KADEMLIAROUTINGINFO_L(infoMsg));

            msg->encapsulate(infoMsg);
        }
    }
    return true;
}
class Comp{
public:
    bool operator()(const KademliaBucketEntry& a, const KademliaBucketEntry& b) {
        return a.getRtt() < b.getRtt();
    }
};




bool Kademlia::cmpRTT(const KademliaBucketEntry& a, const KademliaBucketEntry& b){
    return a.getRtt() < b.getRtt();

}

NodeVector* Kademlia::findNode(const OverlayKey& key, int numRedundantNodes,
                               int numSiblings, BaseOverlayMessage* msg)
{
    if (numSiblings > getMaxNumSiblings()) {
        opp_error("(Kademlia::findNode()) numRedundantNodes or numSiblings "
                  "too big!");

    }

#if 0
    if (numRedundantNodes < 2) {
        throw cRuntimeError("Kademlia::findNode(): For Kademlia "
                                "redundantNodes must be at least 2 "
                                "and lookupMerge should be true!");
    }
#endif

    // create temporary comparator
    KeyDistanceComparator<KeyXorMetric>* comp =
            new KeyDistanceComparator<KeyXorMetric>( key );

    // select result set size
    bool err;
    int resultSize;

    if (numSiblings < 0) {
        // exhaustive iterative doesn't care about siblings
        resultSize = numRedundantNodes;
    } else {
        resultSize = isSiblingFor(thisNode, key, numSiblings, &err) ?
                     (numSiblings ? numSiblings : 1) : numRedundantNodes;
    }
    assert(numSiblings || numRedundantNodes);

    NodeVector* result = new NodeVector(resultSize, comp);

    if (siblingTable->isEmpty()) {
        result->add(thisNode);
        delete comp;
        return result;
    }

    // R/Kademlia: in recursive mode just speed up route messages //TODO iterative PR
    bool returnProxNodes = false;
    if (proximityRouting) {
        if (msg &&
            (!dynamic_cast<FindNodeCall*>(msg->getEncapsulatedPacket()) &&
             !dynamic_cast<FindNodeCall*>(msg))) {
            returnProxNodes = true;
        }
    }

    ProxNodeVector* resultProx = NULL;
    KademliaPRComparator* compProx = NULL;
    if (returnProxNodes) {
        compProx = new KademliaPRComparator(key);
        resultProx = new ProxNodeVector(resultSize, NULL, NULL, compProx, 0, resultSize);
    }

    // add items from buckets
    int index;
    int mainIndex = routingBucketIndex(key);
    int startIndex = routingBucketIndex(key, true);
    int endIndex = routingBucketIndex(siblingTable->back().getKey());

    // add nodes from best fitting bucket
    //
    if (mainIndex != -1) {
        KademliaBucket* bucket = routingTable[mainIndex];
        if (bucket != NULL && bucket->size()) {

            //bucket内の要素iに対して，keyと最も距離が近いものを特定する．
            //OverlayKey minDistance = KeyPrefixMetric().distance(key, bucket->begin()->getKey());

            OverlayKey minDistance = LONG_MAX;
            double currentRTT = -1;
//Added by Kanemitsu START
            if(this->rtt_threshold > 0){
                std::vector<KademliaBucketEntry> rttVector;
                //現在のホップカウントがrtt_threshold以下であれば，という条件

                for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                    //if(j->getRtt() == MAXTIME){
                    if(j->getRtt() >= 100){
                        //もし最大時間が設定されていれば更新させる．
                        //continue;

                    }
                    OverlayKey tmpDistance = KeyPrefixMetric().distance(key, j->getKey());
                    rttVector.push_back(*j);
                    // EV << "kanemitsuKey:" << j->getKey() <<"/RTT:"<<j->getRtt()<<"tmpDistance:"<<tmpDistance<< endl;

                    if(tmpDistance <= minDistance){
                        minDistance = tmpDistance;
                        //currentRTT = SIMTIME_DBL(j->getRtt());
                    }
                }
                std::sort(rttVector.begin(), rttVector.end(),Comp());
                //Comparatorを，RTTの小さい順になるようなものにする．
                //minDistance * 2 (=minDistance << 2)以下であり，かつRTTの小さい順にresultへ格納する．
                //KademliaBucket* rttBucket = new KademliaBucket( k, comparator );
                // create temporary comparator
                //StdProxComparator rttComp = new StdProxComparator();
                //KademliaBucket* rttBucket = new KademliaBucket( k, rttComp );
                //NodeVector* rttResult = new NodeVector(resultSize, rttComp);
                for(std::vector<KademliaBucketEntry>::iterator j=rttVector.begin(); j!=rttVector.end();j++){
                    //for(KademliaBucketEntry itr = rttVector.begin(); itr != rttVector.end(); ++itr) {


                    OverlayKey tmpDistance = KeyPrefixMetric().distance(key, j->getKey());
                    //if(tmpDistance <= (minDistance + minDistance)){
                    if(tmpDistance < (minDistance + minDistance)){
                        //rttResult->add(*j);
                        result->add(*j);
                        if (returnProxNodes)
                            resultProx->add(*j);
                    }
                }
                if(result->isEmpty()){
                    for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                        result->add(*j);
                        if (returnProxNodes)
                            resultProx->add(*j);
                    }
                }
//Added by Kanemitsu END

            }else{
                for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                    result->add(*j);
                    if (returnProxNodes)
                        resultProx->add(*j);
                }
            }



            //RTTの小さい順にする．かつ，distanceがminDistance * 2以下であること．
            //for (KademliaBucket::iterator i=bucket->begin(); i!=bucket->end(); i++) {


            //EV << "kanemitsu:" << i->getKey() << endl;
            /* double val = SIMTIME_DBL(i->getRtt());
             if(val <= minRTT){
                 minRTT = val;
             }
             */
            //i->getRtt();
            //      result->add(*i);
            //      if (returnProxNodes)
            //          resultProx->add(*i);
            //EV << "Kademlia::findNode(): Adding "
            //   << *i << " from bucket " << mainIndex << endl;
            //  }
        }
    }

    // add most fitting buckets
    if (startIndex >= endIndex || !result->isFull()) {
        for (index = startIndex; index >= endIndex; --index) {
            // add bucket to result vector
            if (index == mainIndex) continue;
            KademliaBucket* bucket = routingTable[index];
            if (bucket != NULL && bucket->size()) {
                if(this->rtt_threshold > 0){
                    std::vector<KademliaBucketEntry> rttVector;
                    //現在のホップカウントがrtt_threshold以下であれば，という条件
                    //Kanemitsu START
                    OverlayKey minDistance = LONG_MAX;
                    for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                        //if(j->getRtt() == MAXTIME){
                        if(j->getRtt() >= 100){
                            //もし最大時間が設定されていれば更新させる．
                            //continue;

                        }
                        OverlayKey tmpDistance = KeyPrefixMetric().distance(key, j->getKey());
                        rttVector.push_back(*j);
                        // EV << "kanemitsuKey:" << j->getKey() <<"/RTT:"<<j->getRtt()<<"tmpDistance:"<<tmpDistance<< endl;

                        if(tmpDistance <= minDistance){
                            minDistance = tmpDistance;
                            //currentRTT = SIMTIME_DBL(j->getRtt());
                        }
                    }
                    std::sort(rttVector.begin(), rttVector.end(),Comp());
                    //Comparatorを，RTTの小さい順になるようなものにする．
                    //minDistance * 2 (=minDistance << 2)以下であり，かつRTTの小さい順にresultへ格納する．
                    //KademliaBucket* rttBucket = new KademliaBucket( k, comparator );
                    // create temporary comparator
                    //StdProxComparator rttComp = new StdProxComparator();
                    //KademliaBucket* rttBucket = new KademliaBucket( k, rttComp );
                    //NodeVector* rttResult = new NodeVector(resultSize, rttComp);
                    for(std::vector<KademliaBucketEntry>::iterator j=rttVector.begin(); j!=rttVector.end();j++){
                        //for(KademliaBucketEntry itr = rttVector.begin(); itr != rttVector.end(); ++itr) {


                        OverlayKey tmpDistance = KeyPrefixMetric().distance(key, j->getKey());
                        //if(tmpDistance <= (minDistance + minDistance)){
                        if(tmpDistance < (minDistance + minDistance)){
                            //rttResult->add(*j);
                            result->add(*j);
                            if (returnProxNodes)
                                resultProx->add(*j);
                        }
                    }
                    if(result->isEmpty()){
                        for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                            result->add(*j);
                            if (returnProxNodes)
                                resultProx->add(*j);
                        }
                    }
                    //Kanemitsu END

                }else{
                    for (KademliaBucket::iterator i=bucket->begin(); i!=bucket->end(); i++) {
                        result->add(*i);
                        if (returnProxNodes)
                            resultProx->add(*i);//std::make_pair(*i, i->getRtt()));
                        //EV << "Kademlia::routingGetClosestNodes(): Adding "
                        //   << *i << " from bucket " << index << endl;
                    }
                }

            }
        }

        // add nodes from sibling table
        for (KademliaBucket::iterator i = siblingTable->begin();
             i != siblingTable->end(); i++) {
            result->add(*i);
            if (returnProxNodes)
                resultProx->add(*i);
        }
        // add local node
        result->add(thisNode);
        if (returnProxNodes) {
            KademliaBucketEntry temp = thisNode;
            if (!result->size() || (*result)[0] == thisNode) {
                temp.setProx(Prox::PROX_SELF);
                resultProx->add(temp);
            } else {
                temp.setProx(Prox::PROX_UNKNOWN);
                resultProx->add(temp);
            }
        }
    }

    // add more distant buckets
    for (index = mainIndex + 1; !result->isFull() && index < numBuckets;
         ++index) {
        // add bucket to result vector
        KademliaBucket* bucket = routingTable[index];
        if (bucket != NULL && bucket->size()) {
            if(this->rtt_threshold > 0){
                std::vector<KademliaBucketEntry> rttVector;
                //現在のホップカウントがrtt_threshold以下であれば，という条件
                //Kanemitsu START
                OverlayKey minDistance = LONG_MAX;
                for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                    //if(j->getRtt() == MAXTIME){
                    if(j->getRtt() >= 100){
                        //もし最大時間が設定されていれば更新させる．
                        //continue;

                    }
                    OverlayKey tmpDistance = KeyPrefixMetric().distance(key, j->getKey());
                    rttVector.push_back(*j);
                    // EV << "kanemitsuKey:" << j->getKey() <<"/RTT:"<<j->getRtt()<<"tmpDistance:"<<tmpDistance<< endl;

                    if(tmpDistance <= minDistance){
                        minDistance = tmpDistance;
                        //currentRTT = SIMTIME_DBL(j->getRtt());
                    }
                }
                std::sort(rttVector.begin(), rttVector.end(),Comp());
                //Comparatorを，RTTの小さい順になるようなものにする．
                //minDistance * 2 (=minDistance << 2)以下であり，かつRTTの小さい順にresultへ格納する．
                //KademliaBucket* rttBucket = new KademliaBucket( k, comparator );
                // create temporary comparator
                //StdProxComparator rttComp = new StdProxComparator();
                //KademliaBucket* rttBucket = new KademliaBucket( k, rttComp );
                //NodeVector* rttResult = new NodeVector(resultSize, rttComp);
                for(std::vector<KademliaBucketEntry>::iterator j=rttVector.begin(); j!=rttVector.end();j++){
                    //for(KademliaBucketEntry itr = rttVector.begin(); itr != rttVector.end(); ++itr) {


                    OverlayKey tmpDistance = KeyPrefixMetric().distance(key, j->getKey());
                    //if(tmpDistance <= (minDistance + minDistance)){
                    if(tmpDistance < (minDistance + minDistance)){
                        //rttResult->add(*j);
                        result->add(*j);
                        if (returnProxNodes)
                            resultProx->add(*j);
                    }
                }
                if(result->isEmpty()){
                    for (KademliaBucket::iterator j=bucket->begin(); j!=bucket->end(); j++) {
                        result->add(*j);
                        if (returnProxNodes)
                            resultProx->add(*j);
                    }
                }
                //Kanemitsu END

            }else{
                for (KademliaBucket::iterator i=bucket->begin(); i!=bucket->end(); i++) {
                    result->add(*i);
                    if (returnProxNodes)
                        resultProx->add(*i);
                    //EV << "[Kademlia::routingGetClosestNodes()]\n"
                    //   << "    Adding " << *i << " from bucket " << index
                    //   << endl;
                }
            }

        }
    }

    if (returnProxNodes && resultProx->size() && result->size() &&
        (KeyPrefixMetric().distance(key, (*resultProx)[0].getKey()) <
         KeyPrefixMetric().distance(key, (*result)[0].getKey()))) {
        result->clear();
        for (uint32_t i = 0; i < resultProx->size(); ++i) {
            result->push_back((*resultProx)[i]/*.first*/);
        }
    }
    delete compProx;
    delete resultProx;

    delete comp;

    return result;
}

//-----------------------------------------------------------------------------


void Kademlia::handleTimerEvent(cMessage* msg)
{
    if (msg == bucketRefreshTimer) {
        handleBucketRefreshTimerExpired();
    } else if (msg == siblingPingTimer) {
        if (siblingPingInterval == 0) {
            return;
        }

        for (KademliaBucket::iterator i = siblingTable->begin();
             i != siblingTable->end(); i++) {
            pingNode(*i);
        }
        scheduleAt(simTime() + siblingPingInterval, msg);
    }
}

// R/Kademlia
void Kademlia::handleUDPMessage(BaseOverlayMessage* msg)
{
    // only used for recursive Kademlia
    OverlayCtrlInfo* ctrlInfo =
            check_and_cast<OverlayCtrlInfo*>(msg->removeControlInfo());
    KademliaRoutingInfoMessage* kadRoutingInfoMsg =
            check_and_cast<KademliaRoutingInfoMessage*>(msg);

    routingAdd(kadRoutingInfoMsg->getSrcNode(), true);

    for (uint32_t i = 0; i < kadRoutingInfoMsg->getNextHopsArraySize(); i++) {
        routingAdd(kadRoutingInfoMsg->getNextHops(i),
                   kadRoutingInfoMsg->getNextHops(i).getIsAlive());
    }

    delete ctrlInfo;
    delete msg;
}

//In Kademlia this method is used to maintain the routing table.
bool Kademlia::handleRpcCall(BaseCallMessage* msg)
{
    bool maintenanceLookup = (msg->getStatType() == MAINTENANCE_STAT);
    RPC_SWITCH_START(msg)
    RPC_ON_CALL(Ping) {
        // add active node
        OverlayCtrlInfo* ctrlInfo =
                check_and_cast<OverlayCtrlInfo*>(msg->getControlInfo());
        routingAdd(ctrlInfo->getSrcRoute(), true, MAXTIME, maintenanceLookup);
        break;
    }
    RPC_ON_CALL(FindNode)
    {
        // add active node
        OverlayCtrlInfo* ctrlInfo =
                check_and_cast<OverlayCtrlInfo*>(msg->getControlInfo());
        routingAdd(ctrlInfo->getSrcRoute(), true, MAXTIME, maintenanceLookup);
        break;
    }
    RPC_SWITCH_END()
    return false;
}

//In Kademlia this method is used to maintain the routing table.
void Kademlia::handleRpcResponse(BaseResponseMessage* msg,
                                 cPolymorphic* context, int rpcId,
                                 simtime_t rtt)
{
    bool maintenanceLookup = (msg->getStatType() == MAINTENANCE_STAT);
    OverlayCtrlInfo* ctrlInfo =
            dynamic_cast<OverlayCtrlInfo*>(msg->getControlInfo());
    NodeHandle srcRoute = (ctrlInfo ? ctrlInfo->getSrcRoute()
                                    : msg->getSrcNode());

    RPC_SWITCH_START(msg)
    RPC_ON_RESPONSE(Ping) {
        if (state == INIT) {
            // schedule bucket refresh timer
            cancelEvent(bucketRefreshTimer);
            scheduleAt(simTime(), bucketRefreshTimer);
            cancelEvent(siblingPingTimer);
            scheduleAt(simTime() + siblingPingInterval, siblingPingTimer);
            state = JOIN;
        }
    }
    RPC_ON_RESPONSE(FindNode)
    {
        if (state == INIT) {
            state = JOIN;

            // bootstrap node is trustworthy: add all nodes immediately
            routingAdd(srcRoute, true, rtt, maintenanceLookup);
            for (uint32_t i=0; i<_FindNodeResponse->getClosestNodesArraySize(); i++)
                routingAdd(_FindNodeResponse->getClosestNodes(i), true,
                           MAXTIME-1, maintenanceLookup);

            if (newMaintenance) {
                createLookup()->lookup(getThisNode().getKey(), s, hopCountMax, 0,
                                       new KademliaLookupListener(this));
            } else {
                // schedule bucket refresh timer
                cancelEvent(bucketRefreshTimer);
                scheduleAt(simTime(), bucketRefreshTimer);
                cancelEvent(siblingPingTimer);
                scheduleAt(simTime() + siblingPingInterval, siblingPingTimer);
            }

            break;
        }

        // add active node
        if (defaultRoutingType == SEMI_RECURSIVE_ROUTING ||
            defaultRoutingType == FULL_RECURSIVE_ROUTING ||
            defaultRoutingType == RECURSIVE_SOURCE_ROUTING) {
            rtt = MAXTIME;
        }
        setBucketUsage(srcRoute.getKey());

        // add inactive nodes
        for (uint32_t i=0; i<_FindNodeResponse->getClosestNodesArraySize(); i++)
            routingAdd(_FindNodeResponse->getClosestNodes(i), false,
                       MAXTIME, maintenanceLookup);
        break;
    }
    RPC_SWITCH_END()

    // add node that responded
    routingAdd(srcRoute, true, rtt, maintenanceLookup);
}

// In Kademlia this method is used to maintain the routing table.
void Kademlia::handleRpcTimeout(BaseCallMessage* msg,
                                const TransportAddress& dest,
                                cPolymorphic* context, int rpcId,
                                const OverlayKey& destKey)
{
    if (dest.isUnspecified()) return;
    try {
        RPC_SWITCH_START(msg)
        RPC_ON_CALL(Ping) {
            if (state == INIT) {
                joinOverlay();
                return;
            }

            const NodeHandle& handle = dynamic_cast<const NodeHandle&>(dest);
            routingTimeout(handle.getKey());
            break;
        }
        RPC_ON_CALL(FindNode) {
            if (state == INIT) {
                joinOverlay();
                return;
            }

            const NodeHandle& handle = dynamic_cast<const NodeHandle&>(dest);
            routingTimeout(handle.getKey());
            setBucketUsage(handle.getKey());
            break;
        }
        RPC_SWITCH_END()
    } catch (...) {
        EV << "[Kademlia:handleRpcTimout() @ " << thisNode.getIp()
           << " (" << thisNode.getKey().toString(16) << ")]\n"
           << "    ERROR: RPC timeout without key ("
           << msg << " -> " << dest << ")" << endl;
        return;
    }
}

// R/Kademlia
void Kademlia::proxCallback(const TransportAddress& node, int rpcId,
                            cPolymorphic *contextPointer, Prox prox)
{
    Enter_Method_Silent();

    if (prox != Prox::PROX_TIMEOUT) {
        routingAdd((const NodeHandle&)node, true, prox.proximity);
    } else {
        routingTimeout(((const NodeHandle&)node).getKey());
    }
}

void Kademlia::lookupFinished(bool isValid)
{
    if (state == JOIN) {
        cancelEvent(bucketRefreshTimer);

        if (siblingTable->size() == 0) {
            // initial lookup failed - get new bootstrap node
            joinOverlay();
            return;
        }

        scheduleAt(simTime(), bucketRefreshTimer);

        if (!newMaintenance) {
            state = READY;
            setOverlayReady(true);
        }
    }
}

// handle a expired bucket refresh timer
void Kademlia::handleBucketRefreshTimerExpired()
{
    // refresh buckets
    if (state != READY || (((simTime() - siblingTable->getLastUsage()) >
                            minSiblingTableRefreshInterval))) {
        // R/Kademlia
        if (defaultRoutingType == SEMI_RECURSIVE_ROUTING ||
            defaultRoutingType == FULL_RECURSIVE_ROUTING ||
            defaultRoutingType == RECURSIVE_SOURCE_ROUTING) {
            //TODO real exhaustive-recursive lookup
            createLookup()->lookup(getThisNode().getKey() + OverlayKey::ONE,
                                   0, hopCountMax, 0,
                                   new KademliaLookupListener(this));
        } else if (exhaustiveRefresh) {
            //TODO config shit
            int baseRedundantNodes = iterativeLookupConfig.redundantNodes;
            iterativeLookupConfig.redundantNodes = siblingRefreshNodes;
            createLookup(EXHAUSTIVE_ITERATIVE_ROUTING)->lookup(
                    getThisNode().getKey(), siblingRefreshNodes,
                    hopCountMax, 0, new KademliaLookupListener(this));
            iterativeLookupConfig.redundantNodes = baseRedundantNodes;
        } else if (newMaintenance) {
            //for (KademliaBucket::iterator i = siblingTable->begin();
            //     i != siblingTable->end(); i++) {

            //    sendSiblingFindNodeCall(*i);
            //}
            if (siblingTable->size()) {
                sendSiblingFindNodeCall(siblingTable->at(intuniform(0,siblingTable->size()-1)));
            }
            state = READY;
            setOverlayReady(true);
        } else {
            createLookup()->lookup(getThisNode().getKey(), s, hopCountMax, 0,
                                   new KademliaLookupListener(this));
        }
        siblingTable->setLastUsage(simTime());
        ++siblingTableRefreshCount;
    }

    if (state == READY) {
        if (siblingTable->size()) {
            // get bit index of most significant digit that differs
            // from our next sibling's key to prevent us from refreshing
            // buckets, which can't contain any nodes
            int32_t diff = OverlayKey::getLength() - b*(getThisNode().getKey().
                    sharedPrefixLength(siblingTable->front().getKey(), b) + 1);
            int bucketsRefreshedPerTask = 0;
            for (int32_t i = OverlayKey::getLength() - b; i >= diff; i -=b ) {
                for (int32_t d=0; d < ((1 << b) - 1); d++) {
                    int32_t index = (i / b) * ((1 << b) - 1) + d;
                    if (index < 0) continue;
                    if ((routingTable[index] == NULL) ||
                        ((simTime() - routingTable[index]->getLastUsage()) >
                         minBucketRefreshInterval)) {

                        OverlayKey refreshKey =
                                getThisNode().getKey() ^ (OverlayKey(d+1) << i);

                        // R/Kademlia
                        if (defaultRoutingType == SEMI_RECURSIVE_ROUTING ||
                            defaultRoutingType == FULL_RECURSIVE_ROUTING ||
                            defaultRoutingType == RECURSIVE_SOURCE_ROUTING) {
                            //TODO real exhaustive-recursive lookup
                            createLookup()->lookup(refreshKey, 0,
                                                   hopCountMax, 0,
                                                   new KademliaLookupListener(this));
                        } else if (exhaustiveRefresh) {
                            //TODO config shit
                            int baseRedundantNodes = iterativeLookupConfig.redundantNodes;
                            iterativeLookupConfig.redundantNodes = bucketRefreshNodes;
                            createLookup(EXHAUSTIVE_ITERATIVE_ROUTING)->lookup(
                                    refreshKey, bucketRefreshNodes, hopCountMax,
                                    0, new KademliaLookupListener(this));
                            iterativeLookupConfig.redundantNodes = baseRedundantNodes;
                        } else {
                            createLookup()->lookup(refreshKey, s, hopCountMax, 0,
                                                   new KademliaLookupListener(this));
                        }

                        ++bucketsRefreshedPerTask;
                        ++bucketRefreshCount;
                        setBucketUsage(refreshKey);
                    }
                }
            }
            RECORD_STATS(globalStatistics->recordOutVector(
                    "Kademlia: Buckets Refreshed Per Task",
                    bucketsRefreshedPerTask));
        }
        // schedule next bucket refresh process
        cancelEvent(bucketRefreshTimer);
        scheduleAt(simTime() + (std::min(minSiblingTableRefreshInterval,
                                         minBucketRefreshInterval) / 10.0), bucketRefreshTimer);
    }
}

//virtual public: xor metric
OverlayKey Kademlia::distance(const OverlayKey& x,
                              const OverlayKey& y,
                              bool useAlternative) const
{
    if (!useAlternative) return x^y; // KeyXorMetric().distance(x, y);
    return KeyPrefixMetric().distance(x, y);
}

void Kademlia::updateTooltip()
{
    if (ev.isGUI()) {
        std::stringstream ttString;

        // show our nodeId in a tooltip
        ttString << "This: " << thisNode << endl << "Siblings: "
                 << siblingTable->size();

        getParentModule()->getParentModule()->getDisplayString().
                setTagArg("tt", 0, ttString.str().c_str());
        getParentModule()->getDisplayString().
                setTagArg("tt", 0, ttString.str().c_str());
        getDisplayString().setTagArg("tt", 0, ttString.str().c_str());
    }
}

