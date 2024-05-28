(ns macaw.util)

(defn group-with
  "Generalized `group-by`, where you can supply your own reducing function (instead of usual `conj`).

  https://ask.clojure.org/index.php/12319/can-group-by-be-generalized"
  [kf rf coll]
  (persistent!
    (reduce
      (fn [ret x]
        (let [k (kf x)]
          (assoc! ret k (rf (get ret k) x))))
      (transient {})
      coll)))

(defn seek
  "Like (first (filter ... )), but doesn't realize chunks of the sequence. Returns the first item in `coll` for which
  `pred` returns a truthy value, or `nil` if no such item is found."
  [pred coll]
  (reduce
   (fn [acc x] (if (pred x) (reduced x) acc))
   nil
   coll))

(defn find-relevant
  "Search the given map for the entry corresponding to [[map-key]], considering only the relevant keys.
  The relevant keys are obtained by ignoring any suffix of [[ks]] for which [[map-key]] has nil or missing values.
  We require that there is at least one relevant key to find a match."
  [m map-key ks]
  (when map-key
    (if (every? map-key ks)
      (find m (select-keys map-key ks))
      ;; Strip off keys from right-to-left where they are nil, and relax search to only consider these keys.
      ;; We need at least one non-generate key to remain for the search.
      (when-let [ks-prefix (->> ks reverse (drop-while (comp nil? map-key)) reverse seq)]
        (when (not= ks ks-prefix)
          (seek (comp #{(select-keys map-key ks-prefix)}
                      #(select-keys % ks-prefix)
                      key)
                m))))))

(def ^:private nil-val? (comp nil? val))

(defn strip-nils
  "Remove any keys corresponding to nil values from the given map."
  [m]
  (if (some nil-val? m)
    (with-meta (into {} (remove nil-val?) m) (meta m))
    m))
