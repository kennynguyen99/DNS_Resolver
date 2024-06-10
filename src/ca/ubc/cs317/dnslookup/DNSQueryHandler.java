package ca.ubc.cs317.dnslookup;


import java.io.IOException;
import java.math.BigInteger;
import java.net.*;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

public class DNSQueryHandler {

    private static final int DEFAULT_DNS_PORT = 53;
    private static DatagramSocket socket;
    private static boolean verboseTracing = false;

    private static final Random random = new Random();

    /**
     * Sets up the socket and set the timeout to 5 seconds
     *
     * @throws SocketException if the socket could not be opened, or if there was an
     *                         error with the underlying protocol
     */
    public static void openSocket() throws SocketException {
        socket = new DatagramSocket();
        socket.setSoTimeout(5000);
    }

    /**
     * Closes the socket
     */
    public static void closeSocket() {
        socket.close();
    }

    /**
     * Set verboseTracing to tracing
     */
    public static void setVerboseTracing(boolean tracing) {
        verboseTracing = tracing;
    }

    /**
     * Generate a random transactionID.
     *
     * @return A random transactionID.
     */
    private static short getTransactionID() {

        return (short) (random.nextInt() & 0x7FFF);
    }

    /**
     * Prints a packet
     *
     *
     */
    private static void hexDumpPrint(byte[] message){
        System.out.println("\n\nPRINTING MESSAGE:\n");
        int i = 1;
        for(byte b : message){
            if(i%2==0) {
                System.out.printf("%02X\n", b);
            }else{
                System.out.printf("%02X ", b);

            }
            i++;
        }
        System.out.println("\n\nEND OF MESSAGE:\n");
    }

    /**
     * Output the trace of a query.
     *
     * @param node          DNSNode of query
     * @param server        The InetAddress of the server.
     * @param transactionID The transaction ID
     */
    private static void printTraceQuery(DNSNode node, InetAddress server,
                                        short transactionID) {
        if (verboseTracing) {
            System.out.printf("\n\nQuery ID     %d %s  %s --> %s\n",
                    transactionID, node.getHostName(),
                    node.getType(),
                    server.toString().substring(1));
        }
    }



    /**
     * Builds the query, sends it to the server, and returns the response.
     *
     * @param message Byte array used to store the query to DNS servers.
     * @param server  The IP address of the server to which the query is being sent.
     * @param node    Host and record type to be used for search.
     * @return A DNSServerResponse Object containing the response buffer and the transaction ID.
     * @throws IOException if an IO Exception occurs
     */
    public static DNSServerResponse buildAndSendQuery(byte[] message, InetAddress server,
                                                      DNSNode node) throws IOException {


        short transactionID = getTransactionID();

        // ID
        message[0] = (byte) (transactionID >>8);
        message[1] = (byte) (transactionID);

        // Query count
        message[2] = 0;
        message[3] = 0;


        // Question count
        message[4] = 0;
        message[5] = 1;

        // Answer counts
        for (int i = 6; i < 13; i++) {
            message[i] = 0;
        }

        // write qname
        int indexOffset = 12;
        String hostName = node.getHostName();
        String[] hostNameSplit = hostName.split("\\.");
        for (int i = 0; i < hostNameSplit.length; i++) {
            // write the length of each split part
            message[indexOffset++] = (byte)hostNameSplit[i].length();

            // write the split part in bytes
            byte[] bytes = hostNameSplit[i].getBytes();
            for (int j = 0; j < bytes.length; j++) {
                message[indexOffset++] = bytes[j];
            }
        }

        message[indexOffset++] = 0;

        // write qtype
        message[indexOffset++] = 0;
        message[indexOffset++] = (byte) node.getType().getCode();



        // qclass (always be 0x1 = IN for internet)
        message[indexOffset++] = 0;
        message[indexOffset++] = 1;

        // make a new byte array with the correct size and copy
        byte[] newQuery = new byte[indexOffset];
        for (int i = 0; i < indexOffset; i++) {
            newQuery[i] = message[i];
        }

        if(verboseTracing){
            printTraceQuery(node, server, transactionID);
        }

        DatagramPacket packet = new DatagramPacket(newQuery, indexOffset, server, DEFAULT_DNS_PORT);
        socket.send(packet);

        packet = new DatagramPacket(message, message.length);
        socket.receive(packet);

        byte[] responseMessage = packet.getData();
        ByteBuffer response = ByteBuffer.wrap(responseMessage);

        DNSServerResponse serverResponse = new DNSServerResponse(response, transactionID);
        return serverResponse;
    }


    static class Offset{
        int offset; // offset in bytes
        Offset(int offset){
            this.offset = offset;
        }

        // increment by one byte
        void increment(){this.offset++;}

        void increment(int i){this.offset = this.offset +i;}

        int value(){
            return this.offset;
        }
    }

    /**
     * Decodes the DNS server response and caches it.
     *
     * @param transactionID  Transaction ID of the current communication with the DNS server
     * @param responseBuffer DNS server's response
     * @param cache          To store the decoded server's response
     * @return A set of resource records corresponding to the name servers of the response.
     */
    public static Set<ResourceRecord> decodeAndCacheResponse(int transactionID, ByteBuffer responseBuffer,
                                                             DNSCache cache) {

        ArrayList<ResourceRecord> answers = new ArrayList<>();
        ArrayList<ResourceRecord> nameServers = new ArrayList<>();
        ArrayList<ResourceRecord> additional = new ArrayList<>();
        ArrayList<ResourceRecord> records = new ArrayList<>();

        Offset offset = new Offset(0);

        // parse header
        int returnID = responseBuffer.getShort(offset.value());
        offset.increment(2);

        // parse flags
        int flagCodes = responseBuffer.getShort(offset.value());
        boolean isAuthoritative = (((flagCodes >> 10) & 1) == 1);

        offset.increment(2);

        int QDCount = responseBuffer.getShort(offset.value());
        offset.increment(2);

        int ANCount = responseBuffer.getShort(offset.value());
        offset.increment(2);

        int NSCount = responseBuffer.getShort(offset.value());
        offset.increment(2);

        int ARCount = responseBuffer.getShort(offset.value());
        offset.increment(2);


        // for each section parse each resource record
        DNSNode node = parseQuestionSection(responseBuffer, offset);

        // if the name does not exist, return nothing
        ResourceRecord record;
        if ((flagCodes  & 0xf) == 3){
            return null;
        }

        // parse answer section
        for(int i=0; i<ANCount; i++){
            record = parseResourceRecord(responseBuffer, offset);

            answers.add(record);
            records.add(record);
        }

        // parse name server section
        for(int i=0; i<NSCount; i++){
            record = parseResourceRecord(responseBuffer, offset);

            nameServers.add(record);
            records.add(record);
        }

        // parse additional section
        for(int i=0; i<ARCount; i++){
            record = parseResourceRecord(responseBuffer, offset);

            additional.add(record);
            records.add(record);
        }



        verbosePrintResponse(answers,nameServers, additional, transactionID, isAuthoritative ,ANCount, NSCount, ARCount);

        for(ResourceRecord r: records){
            cache.addResult(r);
        }

        Set<ResourceRecord> returnSet = new HashSet<>(nameServers);
        return returnSet;
    }

    /**
     * Parses a resource record from message
     * Offset will be set to the byte after the record
     *
     * @param messageBuffer  the message
     * @param offset The starting offset of the RR
     * @return The resource record pointed at by offset
     */
    public static ResourceRecord parseResourceRecord(ByteBuffer messageBuffer, Offset offset){
        String name = parseName(messageBuffer, offset);

        // type
        int typeCode = messageBuffer.getShort(offset.value());
        offset.increment(2);

        // class
        offset.increment(2);

        // TTL
        int TTL = messageBuffer.getInt(offset.value());
        offset.increment(4);

        // RD Length
        int RDLength = messageBuffer.getShort(offset.value());
        offset.increment(2);

        RecordType type = RecordType.getByCode(typeCode);

        byte[] IPBytes;

        switch(type){
            // A record
            case A:

                IPBytes = new byte[RDLength];
                System.arraycopy(messageBuffer.array(), offset.value(), IPBytes, 0, RDLength);

                try {
                    InetAddress IPAddress = InetAddress.getByAddress(IPBytes);
                    offset.increment(RDLength);
                    return new ResourceRecord(name, RecordType.A, TTL, IPAddress);
                }catch(Exception e){
                    System.out.println("Error occurred when trying to parse IP address\n");
                }
                break;

            case AAAA:
                IPBytes = new byte[RDLength];
                System.arraycopy(messageBuffer.array(), offset.value(), IPBytes, 0, RDLength);

                try {
                    InetAddress IPAddress = InetAddress.getByAddress(IPBytes);
                    offset.increment(RDLength);
                    return new ResourceRecord(name, RecordType.AAAA, TTL, IPAddress);
                }catch(Exception e){
                    System.out.println("Error occurred when trying to parse IP address\n");
                }
                break;

            case NS:
                // NS record
                String NSServer = parseName(messageBuffer, offset);
                return new ResourceRecord(name, RecordType.NS, TTL, NSServer);
            case CNAME:
                String cname = parseName(messageBuffer, offset);
                return new ResourceRecord(name, RecordType.CNAME, TTL, cname);
            default:
                offset.increment(RDLength);
                return new ResourceRecord(name, type, TTL, "---");
        }


        return null;
    }

    /**
     * Parses the question section
     * Offset will be set to the byte after the question section
     *
     * @param messageBuffer  the message buffer
     * @param offset the starting starting offset of the question section
     * @return The DNS node specifying the question
     */
    public static DNSNode parseQuestionSection(ByteBuffer messageBuffer, Offset offset){

        String domainName = parseName(messageBuffer, offset);

        int qType = messageBuffer.getShort(offset.value());
        offset.increment(2);

        int qClass = messageBuffer.getShort(offset.value());
        offset.increment(2);

        return new DNSNode(domainName, RecordType.getByCode(qType));
    }

    /**
     * Parses the domain name in the resource
     * Offset will be set to the byte after the name
     * Message compression is handled.
     * @param messageBuffer  the message buffer
     * @param offset the starting starting offset of the name
     * @return The name
     */
    public static String parseName(ByteBuffer messageBuffer, Offset offset){
        byte[] message = messageBuffer.array();

        byte curr = message[offset.value()];
        int labelSize;
        String s = "";




        short firstShort;
        while(curr != 0){
            firstShort = messageBuffer.getShort(offset.value());
            if( ((firstShort>>>14) & 3) == 3){
                int pointer = (firstShort & 16383);

                Offset pointerOffset = new Offset(pointer);
                offset.increment(2);
                if(s.equals("")) {
                    return parseName(messageBuffer, pointerOffset);
                }else{
                    return s + parseName(messageBuffer, pointerOffset);
                }


            }

            // how many octets are in this label
            labelSize = message[offset.value()];

            // System.out.format("Label size is %d\n", labelSize);

            offset.increment();


            for(int i=0; i<labelSize; i++){
                s = s + (char)message[offset.value()];
                offset.increment();
            }

            curr = message[offset.value()];

            if(curr!=0){
                s = s + ".";
            }

        }

        offset.increment();
        return s;
    }

    /**
     * Formats and prints the details of the response message (for when trace is on)
     *
     * @param answers The records of the answer section to be printed
     * @param nameServers The records of the name servers section to be printed
     * @param additional The records of the additional section to be printed
     * @param transactionID The transactionID of the response
     * @param isAuthoritative Whether this response is from an authoritative server
     * @param numAnswers The number of answer records in the response
     * @param numNameServers The number of name servers records in the response
     * @param numAdditional The number of additional records (A, AAAA, CNAME etc...) in response
     */

    public static void verbosePrintResponse(ArrayList<ResourceRecord> answers, ArrayList<ResourceRecord> nameServers,
                                            ArrayList<ResourceRecord> additional, int transactionID, boolean isAuthoritative,
                                            int numAnswers, int numNameServers, int numAdditional){
        if(!verboseTracing)
            return;
        if(isAuthoritative) {
            System.out.format("Response ID: %d Authoritative = true\n", transactionID);
        }else{
            System.out.format("Response ID: %d Authoritative = false\n", transactionID);
        }

        System.out.format("  Answers (%d)\n", numAnswers);
        for(ResourceRecord r : answers){
            verbosePrintResourceRecord(r, r.getType().getCode());

        }

        System.out.format("  Nameservers (%d)\n", numNameServers);
        for(ResourceRecord r : nameServers){
            verbosePrintResourceRecord(r, r.getType().getCode());

        }

        System.out.format("  Additional Information (%d)\n", numAdditional);
        for(ResourceRecord r : additional){
            verbosePrintResourceRecord(r, r.getType().getCode());

        }
    }


    /**
     * Formats and prints record details (for when trace is on)
     *
     * @param record The record to be printed
     * @param rtype  The type of the record to be printed
     */
    private static void verbosePrintResourceRecord(ResourceRecord record, int rtype) {
        if (verboseTracing)
            System.out.format("       %-30s %-10d %-4s %s\n", record.getHostName(),
                    record.getTTL(),
                    record.getType() == RecordType.OTHER ? rtype : record.getType(),
                    record.getTextResult());
    }
}