/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package s2i;

import com.sun.istack.internal.FinalArrayList;
import dataset.SpatialKeywordTuple;
import framework.SpatioTextualObject;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.TreeSet;
import util.file.BufferedListStorage;
import util.file.ColumnFileException;
import util.file.DataNotFoundException;
import util.file.PersistentHashMap;
import util.file.EntryStorage;
import util.file.IntegerEntry;
import util.file.MetadataStorage;
import util.nra.NRA;
import util.nra.Source;
import util.sse.SSEExeption;
import util.sse.Term;
import util.sse.Vector;
import util.sse.Vocabulary;
import util.statistics.StatisticCenter;
import xxl.core.cursors.Cursor;
import xxl.util.MaxDoubleRTree;
import xxl.util.MaxDoubleRectangle;
import xxl.core.io.converters.IntegerConverter;
import xxl.core.spatial.KPE;
import xxl.core.spatial.points.DoublePoint;
import xxl.core.spatial.rectangles.DoublePointRectangle;
import xxl.util.StarRTree;

/**
 *
 * @author joao
 */
public class SpatialInvertedIndex {
    //Vocabulary that maps terms to an id.

    protected Vocabulary termVocabulary;
    //maps term id (from termVocabulary) to the number of documents that has the term (document frequency of the term)
    protected EntryStorage<IntegerEntry> termInfo;
    protected MetadataStorage<IntegerEntry> info;
    private final StatisticCenter statisticCenter;
    private final String outputPath;
    //Maps term_id:termType, the type can be FILE_TYPE or TREE_TYPE;
    protected static final int FILE_TYPE = 0; //Items managed by the FileTermManager
    protected static final int TREE_TYPE = 1; //Items managed by the TreeTermManaagerCache
    protected final PersistentHashMap<Integer, Integer> termType;
    protected final FileTermManager fileTermManager;
    protected TreeTermManager treeTermManager;
    private BufferedListStorage<SpatioItem> fileTreeStore; //Used only in constructionTime
    private final int blockCapacity; //Stores the capacity (number of objects) that can be stored in a block
    private final boolean constructionTime;
    private int dataSetSize = -1;

    public SpatialInvertedIndex(StatisticCenter statisticCenter, String outputPath,
            int blockSize, int treeDimensions, int treeCacheSize,
            int treeNodeMinCapacity, int treeNodeMaxCapacity, int fileCacheSize,
            int treesOppened, boolean constructionTime) {

        this.statisticCenter = statisticCenter;
        this.outputPath = outputPath;
        this.termType = new PersistentHashMap<Integer, Integer>(outputPath + "/termType.obj");

        this.fileTermManager = new FileTermManager(statisticCenter, blockSize, outputPath + "/s2i", fileCacheSize);

        this.blockCapacity = blockSize / SpatioItem.SIZE;
        this.constructionTime = constructionTime;

        if (constructionTime) {
            fileTreeStore = new BufferedListStorage<SpatioItem>(statisticCenter,
                    "fileTreeStore", outputPath + "/tmpFiles", treesOppened,
                    SpatioItem.SIZE, SpatioItem.FACTORY);

            this.treeTermManager = new TreeTermManager(statisticCenter, outputPath,
                    treeDimensions, treesOppened * treeCacheSize, blockSize, treeNodeMinCapacity,
                    treeNodeMaxCapacity, 1 /*treesOppened*/);
        } else {
            this.treeTermManager = new TreeTermManager(statisticCenter, outputPath,
                    treeDimensions, treeCacheSize, blockSize, treeNodeMinCapacity,
                    treeNodeMaxCapacity, treesOppened);
        }
    }

    public void open() throws SSEExeption, ColumnFileException, IOException, ClassNotFoundException {
        termType.open();

        termVocabulary = new Vocabulary(outputPath + "/termVocabulary.txt");
        termVocabulary.open();

        termInfo = new EntryStorage<IntegerEntry>(statisticCenter, "termInfo",
                outputPath + "/termInfo", IntegerEntry.SIZE, IntegerEntry.FACTORY);
        termInfo.open();

        info = new MetadataStorage<IntegerEntry>(outputPath + "/info", IntegerEntry.SIZE, IntegerEntry.FACTORY);
        info.open();

        fileTermManager.open();

        if (constructionTime) {
            fileTreeStore.open();
        } else {
            //Open in the method buildTrees.
            treeTermManager.open();
        }
    }

    public boolean isConstructionTime() {
        return constructionTime;
    }

    public void insert(int id, double latitude, double longitude, String text) throws SSEExeption, IOException, ColumnFileException, ClassNotFoundException {
        Vector vector = new Vector(id);
        int numWords = Vector.vectorize(vector, text, termVocabulary);
        System.out.println("Numero de palavras: " + numWords);
        statisticCenter.getCount("totalNumberOfWords").update(numWords);
        statisticCenter.getTally("avgNumDistinctTerms").update(vector.size());
        insert(id, latitude, longitude, vector);
    }

    public void insert(int id, double latitude, double longitude, Vector vector) throws SSEExeption, IOException, ColumnFileException, ClassNotFoundException {
        dataSetSize = -1; //Force update during execution of method getDataSetSize()

        double docLength = Vector.computeDocWeight(vector);

        IntegerEntry entry;
        Iterator<Term> terms = vector.iterator();
        Term term;
        Integer type;
        while (terms.hasNext()) {
            term = terms.next();
            //We normalize weight by the document lenght, which gives the impact of t
            term.setWeight(term.getWeight() / docLength);

            List<SpatioItem> list;
            type = termType.get(term.getTermId());
            if (type == null || type == FILE_TYPE) {
                list = fileTermManager.getList(term.getTermId(), false);
                if (list == null) {
                    list = new ArrayList<SpatioItem>();
                }

                list.add(new SpatioItem(id, latitude, longitude, term.getWeight()));
                if (list.size() > blockCapacity) { //moves all terms stored in the file to the tree
                    termType.put(term.getTermId(), TREE_TYPE);
                    fileTermManager.remove(term.getTermId());
                    insertTree(term.getTermId(), list);
                } else {
                    termType.put(term.getTermId(), FILE_TYPE);
                    fileTermManager.putList(term.getTermId(), list, false);
                }
            } else {
                list = new ArrayList<SpatioItem>(1);
                list.add(new SpatioItem(id, latitude, longitude, term.getWeight()));
                insertTree(term.getTermId(), list);
            }

            //Update the df (document frequency) of the term
            entry = termInfo.getEntry(term.getTermId());
            termInfo.putEntry(term.getTermId(), entry == null ? new IntegerEntry(1)
                    : new IntegerEntry(entry.getValue() + 1));
        }

        //Update the datasetSize
        entry = info.getEntry();
        info.putEntry(entry == null ? new IntegerEntry(1)
                : new IntegerEntry(entry.getValue() + 1));
    }

    private void insertTree(int termId, List<SpatioItem> newList) throws IOException, ClassNotFoundException, ColumnFileException {
        if (constructionTime) {
            fileTreeStore.addList(termId, newList, false);
        } else {
            MaxDoubleRTree tree = treeTermManager.get(termId);
            insert(tree, newList);
        }
    }

    private void insert(MaxDoubleRTree tree, List<SpatioItem> list) {
        for (SpatioTextualObject entry : list) {
            tree.insert(new KPE(
                    new MaxDoubleRectangle(
                    new double[]{entry.getLatitude(), entry.getLongitude()},
                    new double[]{entry.getLatitude(), entry.getLongitude()},
                    entry.getScore()),
                    entry.getId(), IntegerConverter.DEFAULT_INSTANCE));
        }
    }

    /**
     * The score of the objects is the textual score that is the sum of
     * termImpact*(queryTermWeight/queryLength) for each term in the
     * queryKeywords. methods getSource...
     */
    public Iterator<SpatioTextualObject> query(double[] minCoordinate,
            /*REMOVER*/ double[] maxCoordinate, String queryKeywords) throws SSEExeption,
            IOException, ClassNotFoundException, ColumnFileException, DataNotFoundException {

        Vector queryVector = new Vector();
        Vector.vectorize(queryVector, queryKeywords, termVocabulary);
        double queryLength = Vector.computeQueryWeight(queryVector, getDatasetSize(), termInfo);

        SpatioTextualObject resultItem, item;
        final LinkedHashMap<Integer, SpatioTextualObject> resultSet;
        resultSet = new LinkedHashMap<Integer, SpatioTextualObject>();

        Source<SpatioItem>[] sources = new Source[queryVector.size()];

        Iterator<Term> it = queryVector.iterator();
        Term queryTerm;
        Integer type = null;
        for (int i = 0; it.hasNext(); i++) {
            queryTerm = it.next();

            type = termType.get(queryTerm.getTermId());
            if (type != null) {
                if (type == TREE_TYPE) {
                    sources[i] = treeTermManager.getSource(queryTerm,
                            new DoublePointRectangle(new DoublePoint(minCoordinate),
                            new DoublePoint(maxCoordinate)));
                } else {
                    sources[i] = fileTermManager.getSource(queryTerm,
                            new DoublePointRectangle(new DoublePoint(minCoordinate),
                            new DoublePoint(maxCoordinate)));
                }

            } else {
                sources[i] = new Source<SpatioItem>() {
                    public SpatioItem next() {
                        return null;
                    }
                };
                System.out.println("term='" + termVocabulary.getTerm(queryTerm.getTermId()) + "' was not indexed!");
            }

            //Aggregate the scores of the objects received from different sources
            while ((item = sources[i].next()) != null) {
                resultItem = resultSet.get(item.getId());
                if (resultItem == null) {
                    resultItem = new SpatioItem(item.getId(), item.getLatitude(),
                            item.getLongitude(), 0);
                    resultSet.put(item.getId(), resultItem);
                }
                ((SpatioItem) resultItem).setScore(resultItem.getScore()
                        + item.getScore()/*TermImpact()*/ * (queryTerm.getWeight() / queryLength));
            }
        }

        return resultSet.values().iterator();
    }

    public Iterator<SpatialKeywordTuple> SPKQSearch(double latitude, double longitude, double range, double maxDist, String queryKeywords,
            double alpha) throws SSEExeption, IOException, ClassNotFoundException, ColumnFileException, DataNotFoundException {

        HashMap finalTopK = new HashMap();
        TreeSet<SpatialKeywordTuple> result = new TreeSet<>();
        Vector queryVector = new Vector();

        Vector.vectorize(queryVector, queryKeywords, termVocabulary); //número de termos da consulta = 1

        double queryLength = Vector.computeQueryWeight(queryVector, getDatasetSize(), termInfo);

        Iterator<Term> it = queryVector.iterator();
        Term queryTerm;
        Integer type;

        int flag = 0;

        for (int i = 0; it.hasNext(); i++) {

            ArrayList<SpatioItem> partialTopK;
            queryTerm = it.next();

            type = termType.get(queryTerm.getTermId());

            if (type != null) {
                if (type == TREE_TYPE) {
                    System.out.println("Tree");
                    partialTopK = treeTermManager.getRangeSource(queryTerm, queryVector.size(), queryLength,
                            latitude, longitude, maxDist, alpha, range);
                    flag++;
                } else {
                    System.out.println("File");
                    partialTopK = fileTermManager.getRangeSource(queryTerm, queryVector.size(), queryLength,
                            latitude, longitude, maxDist, alpha, range);
                    flag++;
                }
            } else {
                return null;
            }

            if (flag == 1) {
                for (SpatioItem teste : partialTopK) {
                    finalTopK.put(teste.getId(), teste);
                }
            } else {
                for (int j = 0; j < partialTopK.size(); j++) {

                    if (finalTopK.containsKey(partialTopK.get(j).getId())) {

                        double partialScore = partialTopK.get(j).getScore();
                        SpatioItem aux = (SpatioItem) finalTopK.get(partialTopK.get(j).getId());
                        double finalScore = partialScore + aux.getScore();
                        aux.setScore(finalScore);

                        finalTopK.put(partialTopK.get(j).getId(), aux);

                    } else {
                        finalTopK.put(partialTopK.get(j).getId(), partialTopK.get(j));
                    }
                }
            }
        }

        //ordenando os features pelo esccore
        Collection collection = finalTopK.values();
        Iterator iterator = collection.iterator();         

        while (iterator.hasNext()) {
            SpatioItem obj = (SpatioItem) iterator.next();

            SpatialKeywordTuple bestFeature = new SpatialKeywordTuple(null, "texto não informado", obj.getId(), obj.getScore());
            bestFeature.setLatitude(obj.getLatitude());
            bestFeature.setLongitude(obj.getLongitude());
            bestFeature.setDistanciaObjetoInteresse(obj.getDistancia());

            result.add(bestFeature);
        }

        return result.descendingIterator();
    }

    public TreeSet<SpatialKeywordTuple> SPKQPlusSearch(double range, double maxDist, String queryKeywords, double alpha, StarRTree interestTree, final int k) throws SSEExeption,
            IOException, ClassNotFoundException, ColumnFileException, DataNotFoundException {

        Vector queryVector = new Vector();
        Vector.vectorize(queryVector, queryKeywords, termVocabulary); //número de termos da consulta = 1

        double queryLength = Vector.computeQueryWeight(queryVector, getDatasetSize(), termInfo);

        TreeSet<SpatialKeywordTuple> results = new TreeSet<>();
        ArrayList<SpatioTreeHeapEntry> conjuntoV;
        ArrayList<SpatioTreeHeapEntry> partialTopK;
        HashMap finalTopK = new HashMap();

        //Cursor apontando para as folhas
        Cursor leaves = interestTree.query(1);

        SpatioTreeHeapEntry leafEntry = null;

        //para cada V
        while (leaves.hasNext()) {

            Iterator<Term> it = queryVector.iterator();
            Term queryTerm;
            Integer type = null;

            leafEntry = new SpatioTreeHeapEntry(leaves.next());

            Cursor interestPointer = interestTree.query(leafEntry.getMBR());

            //constroi o V            
            conjuntoV = new ArrayList<>();
            conjuntoV.clear();

            while (interestPointer.hasNext()) {
                SpatioTreeHeapEntry interestObject = new SpatioTreeHeapEntry(interestPointer.next());
                conjuntoV.add(interestObject);
            }

            int flag = 0;
            //percorre as árvores de cada termo da consulta
            for (int i = 0; it.hasNext(); i++) {
                System.out.println("Cont: " + i);
                queryTerm = it.next();

                type = termType.get(queryTerm.getTermId());
                partialTopK = new ArrayList<>();

                if (type != null) {
                    if (type == TREE_TYPE) {
                        System.out.println("Tree");
                        flag++;
                        partialTopK = treeTermManager.getRangeSourcePlus(queryTerm, dataSetSize, queryLength, conjuntoV, maxDist, alpha, range);
                    } else {
                        System.out.println("File");
                        flag++;
                        partialTopK = fileTermManager.getRangeSourcePlus(queryTerm, dataSetSize, queryLength, conjuntoV, maxDist, alpha, range);
                    }
                } else { //precisa disso?             
                    return null;
                }

                //juntando os escores 
                if (flag == 1) {
                    for (SpatioTreeHeapEntry teste : partialTopK) {
                        finalTopK.put(teste.getId(), teste);
                    }
                } else {
                    for (int j = 0; j < partialTopK.size(); j++) {

                        if (finalTopK.containsKey(partialTopK.get(j).getId())) {

                            double partialScore = partialTopK.get(j).getScore();
                            SpatioTreeHeapEntry aux = (SpatioTreeHeapEntry) finalTopK.get(partialTopK.get(j).getId());
                            double finalScore = partialScore + aux.getScore();
                            aux.setScore(finalScore);

                            finalTopK.put(partialTopK.get(j).getId(), aux);

                        } else {
                            finalTopK.put(partialTopK.get(j).getId(), partialTopK.get(j));
                        }
                    }
                }
            }

            Collection collection = finalTopK.values();
            Iterator iterator = collection.iterator();
            
            //Atualiza os K melhores
            while(iterator.hasNext()) {

                SpatioTreeHeapEntry entry = (SpatioTreeHeapEntry) iterator.next();

                if (entry.getScore() == -1) {
                    entry.setScore(0);
                }

                double[] coord = {entry.getMBR().getCorner(false).getValue(0),
                    entry.getMBR().getCorner(false).getValue(1)};

                SpatialKeywordTuple novo = new SpatialKeywordTuple(coord, " ", entry.getId(), entry.getScore());
                novo.setLatitude(coord[0]);
                novo.setLongitude(coord[1]);

                if (results.size() < k) {
                    results.add(novo);
                } else if (novo.getScore() > results.first().getScore()) {
                    results.pollFirst();
                    results.add(novo);
                }
            }
        }
        return results;
    }

    public Iterator<SpatioTextualObject> search(double latitude,
            double longitude, double maxDist, String queryKeywords, int k, double alpha) throws SSEExeption,
            IOException, ClassNotFoundException, ColumnFileException, DataNotFoundException {

        Vector queryVector = new Vector();
        Vector.vectorize(queryVector, queryKeywords, termVocabulary);
        double queryLength = Vector.computeQueryWeight(queryVector, getDatasetSize(), termInfo);

        Source<SpatioItem>[] sources = new Source[queryVector.size()];

        Iterator<Term> it = queryVector.iterator();
        Term queryTerm;
        Integer type = null;

        for (int i = 0; it.hasNext(); i++) {
            queryTerm = it.next();

            type = termType.get(queryTerm.getTermId());
            if (type != null) {
                if (type == TREE_TYPE) {
                    sources[i] = treeTermManager.getSource(queryTerm, queryVector.size(), queryLength,
                            new DoublePoint(new double[]{latitude, longitude}), maxDist, alpha);
                } else {
                    sources[i] = fileTermManager.getSource(queryTerm, queryVector.size(), queryLength,
                            new DoublePoint(new double[]{latitude, longitude}), maxDist, alpha);
                }
            } else {
                sources[i] = new Source<SpatioItem>() {
                    public SpatioItem next() {
                        return null;
                    }
                };
                System.out.println("term='" + termVocabulary.getTerm(queryTerm.getTermId()) + "' was not indexed!");
            }
        }
//acrescentar metodo aqui para remover os objetos que nao estao no range
        NRA<SpatioItem> nra = new NRA<SpatioItem>(sources, k);
        nra.run();

        final Iterator<SpatioItem> result = nra.getResult();

        return new Iterator<SpatioTextualObject>() {
            public boolean hasNext() {
                return result.hasNext();
            }

            public SpatioTextualObject next() {
                return result.next();
            }

            public void remove() {
                throw new UnsupportedOperationException("Not supported yet.");
            }
        };
    }

    /**
     * @param STATUS_TIME
     * @return the number of trees constructed.
     * @throws ColumnFileException
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public int buildTrees(long STATUS_TIME) throws ColumnFileException, IOException, ClassNotFoundException {
        treeTermManager.open();
        long time = System.currentTimeMillis();
        int count = 0;
        fileTreeStore.resetCacheSize(0);
        List<Integer> ids = fileTreeStore.getIds();
        int totalSize = ids.size();
        for (int termId : ids) {
            //System.out.println(termId);
            MaxDoubleRTree tree = treeTermManager.get(termId);
            insert(tree, fileTreeStore.getList(termId));
            count++;
            if ((System.currentTimeMillis() - time) > STATUS_TIME) {
                time = System.currentTimeMillis();
                System.out.print("[" + count + "/" + totalSize + "] ");
            }
        }
        System.out.println("\nRemoving the temporary file created during indexing...");
        fileTreeStore.delete();
        return count;
    }

    /*
     static double score(Term queryTerm, double queryLenght,
     double distanceToQueryPoint, Term docTerm, double maxDistance, double alpha){

     double distance = distanceToQueryPoint/maxDistance;

     double textRelevance=docTerm.getWeight()*(queryTerm.getWeight()/queryLenght);

     return alpha*textRelevance/(alpha + distance);

     }
     */
    /**
     * Score of a term
     *
     * @return
     */
    static double textualPartialScore(double queryWeight, double queryLenght,
            double docTermWeight, double alpha) {

        double textRelevance = docTermWeight * (queryWeight / queryLenght); // X = queryTerm.getWeight()/ Wtqd = Vector.computeQueryWeight();

        //return (1 - alpha) * textRelevance;
        return (1 - alpha) * textRelevance;
    }

    static double spatioPartialScore(int queryKeywords,
            double distanceToQueryPoint, double maxDistance, double alpha) {
        double spatialProximity = 1 - (distanceToQueryPoint / maxDistance);

        return alpha * spatialProximity / (double) queryKeywords;
    }

    /**
     * @return the termVocabulary
     */
    public Vocabulary getTermVocabulary() {
        return termVocabulary;
    }

    public int getDocumentFrequency(int termId) throws SSEExeption, IOException, ColumnFileException, DataNotFoundException {
        return termInfo.getEntry(termId).getValue();
    }

    public long getNumDistinctTerms() {
        return termVocabulary.size();
    }

    public int getDatasetSize() throws SSEExeption, IOException, ColumnFileException, DataNotFoundException {
        if (dataSetSize == -1) {
            IntegerEntry entry = info.getEntry();
            dataSetSize = entry == null ? 0 : entry.getValue();
        }
        return dataSetSize;
    }

    public long getFileManagerSizeInBytes() throws ColumnFileException, IOException, DataNotFoundException {
        return fileTermManager.getSizeInBytes();
    }

    public long getTreeManagerSizeInBytes() {
        return treeTermManager.getSizeInBytes();
    }

    public long getSizeInBytes() throws ColumnFileException, DataNotFoundException, IOException {
        return fileTermManager.getSizeInBytes() + treeTermManager.getSizeInBytes();
    }

    public void flush() throws ColumnFileException, IOException {
        fileTermManager.flush();
        treeTermManager.flush();
    }

    public void close() throws SSEExeption, ColumnFileException, IOException {
        termVocabulary.close();
        termInfo.close();

        info.close();

        termType.close();

        fileTermManager.close();

        treeTermManager.close();
    }
}
